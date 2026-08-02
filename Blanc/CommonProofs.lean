-- CommonProofs.lean : proof layers downstream of Blanc's tactic machinery.

import Blanc.Tactics

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

lemma not_run_rev {c e s r} : ¬ Func.Run c e s Func.rev r := by
  intro h
  cases h with
  | last h_run =>
    simp only [Linst.Run, Linst.run] at h_run
    rcases of_bind_eq_ok h_run with ⟨v1, h1, h2⟩
    rcases of_bind_eq_ok h2 with ⟨v2, h3, h4⟩
    rcases of_bind_eq_ok h4 with ⟨v3, h5, h6⟩
    contradiction

lemma of_run_branch_rev {c e s r} {p : Func} (h : Func.Run c e s (.rev <?> p) r) :
    ∃ s', Devm.PopBurn [0] s s' ∧ Func.Run c e s' p r := by
  rcases of_run_branch h with ⟨s', h_pb, h_run⟩ | ⟨w, s', s'', h_ne, h_pb, h_b, h_run⟩
  · exact ⟨s', h_pb, h_run⟩
  · exfalso; exact not_run_rev h_run

lemma dispatchWith_inv {c k f}
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    ( h0 :
      ∀ {e s x w s' s''},
        σ e s →
        Line.Run e s [pushB256 x, eq] s' →
        Devm.PopBurn [w] s' s'' →
        σ e s'' )
    ( h1 :
      ∀ {e s x w s' s''},
        σ e s →
        Line.Run e s [dup 0, pushB256 x, gt] s' →
        Devm.PopBurn [w] s' s'' →
        σ e s'' )
    (h2 : c[k]? = some f)
    (h3 : ∀ {e s s' r}, σ e s → Devm.Burn s s' → Func.Run c e s' f r → ρ e r) :
    ∀ t : DispatchTree,
      (∀ {e s r}, ∀ wf ∈ t, σ e s → Func.Run c e s wf.2 r → ρ e r) →
    ∀ (e s r), σ e s → Func.Run c e s (dispatchWith k t) r → ρ e r := by
  intro t
  induction t with
  | fork t t' ih ih' =>
    intro htt' e s r hs
    have ht : ∀ {e s r}, ∀ wp ∈ t, σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ (Or.inl h_in)
    have ht' : ∀ {e s r}, ∀ wp ∈ t', σ e s → Func.Run c e s wp.2 r → ρ e r := by
      intro e s r wp h_in; apply htt' _ (Or.inr h_in)
    func_execute 3; intro h₂
    rcases of_run_branch h₂ with ⟨s₂, h_pop, h_run'⟩ | ⟨w, s₂, s₃, hw, h_pop, h_burn, h_run'⟩
    · apply ih' ht' e s₂ r (h1 hs h₁ h_pop) h_run'
    · apply ih ht e s₃ r (h1 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'
  | leaf w p =>
    intro htt' e s r hs
    func_execute 2; intro h'
    rcases of_run_branch h' with ⟨s₂, h_pop, h_run'⟩ | ⟨w', s₂, s₃, hw', h_pop, h_burn, h_run'⟩
    · cases h_run' with
      | call h_eq_f h_burn' h_run_f =>
        have hh := Eq.trans h2.symm h_eq_f
        injection hh with heq
        subst heq
        apply h3 (h0 hs h₁ h_pop) h_burn' h_run_f
    · apply htt' ⟨w, p⟩ rfl (h0 hs h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run'

def ifOk {ε α} (π : α → Prop) : Except ε α → Prop
  | .error _ => True
  | .ok a => π a

def Prog.At (p : Prog) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (devm : Devm) : Prop :=
  some (devm.getCode ca).toList = Prog.compile p ∧
  (sevm.currentTarget = ca → (some sevm.code.toList = Prog.compile p ∧ pc = 0))

def ForallSubExec (k : Nat) (ca : Adr) (p : Prog)
    (R : Sevm → Devm → Devm → Prop) : Prop :=
  ∀ pc sevm devm post,
    Exec pc sevm devm (.ok post) →
    sevm.depth < k →
    p.At ca pc sevm devm →
    R sevm devm post

def Exec.Wkn (ca : Adr) (p : Prog)
    (π : Exec.Pred)
    (pc sevm devm exn) (ex : Exec pc sevm devm exn) : Prop :=
  p.At ca pc sevm devm → π pc sevm devm exn ex

def ForallDeeper (k : Nat) (ε : Exec.Pred) : Prop :=
  ∀ pc sevm devm exn (ex : Exec pc sevm devm exn), sevm.depth < k → ε pc sevm devm exn ex

def ForallDeeperAt (k : Nat) (ca : Adr) (p : Prog) (ε : Exec.Pred) : Prop :=
  ForallDeeper k (fun pc sevm devm exn ex => p.At ca pc sevm devm → ε pc sevm devm exn ex)

lemma State.setBal_getCode (st : State) (adr a : Adr) (val : B256) :
  (st.setBal adr val).getCode a = st.getCode a := by
  dsimp [State.setBal, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      dsimp [Acct.withBal]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma State.addBal_getCode (st : State) (adr a : Adr) (val : B256) :
  (st.addBal adr val).getCode a = st.getCode a := by
  dsimp [State.addBal]
  exact State.setBal_getCode st adr a (st.bal adr + val)

lemma State.subBal_getCode {st st' : State} {adr a : Adr} {val : B256} (h : st.subBal adr val = some st') :
  st'.getCode a = st.getCode a := by
  dsimp [State.subBal] at h
  split at h
  · contradiction
  · injection h with h2
    subst h2
    exact State.setBal_getCode st adr a (st.bal adr - val)

lemma Benv.addBal_getCode (benv : Benv) (adr a : Adr) (val : B256) :
  (benv.addBal adr val).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.addBal, Benv.withState]
  exact State.addBal_getCode benv.state adr a val

lemma Benv.subBal_getCode {benv benv' : Benv} {adr a : Adr} {val : B256} (h : benv.subBal adr val = some benv') :
  benv'.state.getCode a = benv.state.getCode a := by
  dsimp [Benv.subBal, Option.bind] at h
  split at h
  · contradiction
  · rename_i st' h_sub
    injection h with h2
    subst h2
    dsimp [Benv.withState]
    exact State.subBal_getCode h_sub

/-! The solvency-facing world relation. -/

def Devm.WorldEq (d d' : Devm) : Prop :=
  d.state = d'.state ∧ d.transientStorage = d'.transientStorage

lemma Devm.worldEq_setMach (d : Devm) (mach : Mach) :
    Devm.WorldEq d (d.setMach mach) := by
  exact ⟨rfl, rfl⟩

lemma liftMachPure_worldEq (core : Mach → Mach) (d : Devm) :
    Devm.WorldEq d (liftMachPure core d) := by
  exact Devm.worldEq_setMach d _

lemma liftMachMetaPure_worldEq
    (core : Mach → Meta → Mach × Meta) (d : Devm) :
    Devm.WorldEq d (liftMachMetaPure core d) := by
  exact ⟨rfl, rfl⟩

lemma addAccessedAddress_worldEq (d : Devm) (a : Adr) :
    Devm.WorldEq d (addAccessedAddress d a) := by
  exact liftMachMetaPure_worldEq _ _

lemma addAccessedStorageKey_worldEq (d : Devm) (a : Adr) (k : B256) :
    Devm.WorldEq d (addAccessedStorageKey d a k) := by
  exact liftMachMetaPure_worldEq _ _

lemma liftMach_worldEq_of_ok {core : Mach → Footprint.Outcome Mach α}
    {d d' : Devm} {x : α} (h : liftMach core d = .ok (x, d')) :
    Devm.WorldEq d d' := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error err => simp [hc] at h
  | ok out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.worldEq_setMach d out.2

lemma liftMach_worldEq_of_error {core : Mach → Footprint.Outcome Mach α}
    {d : Devm} {err : EvmError × Devm} (h : liftMach core d = .error err) :
    Devm.WorldEq d err.2 := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    exact Devm.worldEq_setMach d out.2
  | ok out => simp [hc] at h

lemma liftMachExecution_worldEq_of_ok {core : Mach → Footprint.Outcome Mach Unit}
    {d d' : Devm} (h : liftMachExecution core d = .ok d') :
    Devm.WorldEq d d' := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i out heq
    cases h
    exact liftMach_worldEq_of_ok heq

lemma liftMachExecution_worldEq_of_error {core : Mach → Footprint.Outcome Mach Unit}
    {d : Devm} {err : EvmError × Devm} (h : liftMachExecution core d = .error err) :
    Devm.WorldEq d err.2 := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · rename_i e heq
    cases h
    exact liftMach_worldEq_of_error heq
  · cases h

lemma chargeGas_worldEq_of_ok {cost : Nat} {d d' : Devm}
    (h : chargeGas cost d = .ok d') : Devm.WorldEq d d' := by
  exact liftMachExecution_worldEq_of_ok (core := Mach.chargeGas cost) h

lemma chargeGas_worldEq_of_error {cost : Nat} {d : Devm} {err : EvmError × Devm}
    (h : chargeGas cost d = .error err) : Devm.WorldEq d err.2 := by
  exact liftMachExecution_worldEq_of_error (core := Mach.chargeGas cost) h

lemma Devm.WorldEq.getCode {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getCode a = d'.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h.1]

lemma Devm.WorldEq.getBal {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    d.getBal a = d'.getBal a := by
  unfold Devm.getBal Devm.getAcct
  rw [h.1]

lemma addAccessedAddress_getCode {devm : Devm} {adr a : Adr} :
    (addAccessedAddress devm adr).getCode a = devm.getCode a := by
  exact (addAccessedAddress_worldEq devm adr).getCode a |>.symm

lemma chargeGas_getCode {devm devm' : Devm} {cost : ℕ} {a : Adr}
    (h : chargeGas cost devm = Except.ok devm') :
    devm'.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma Devm.pop_worldEq_of_ok {devm devm' : Devm} {x : B256}
    (h : devm.pop = .ok (x, devm')) : Devm.WorldEq devm devm' := by
  exact liftMach_worldEq_of_ok (core := Mach.pop) h

lemma Devm.pop_getCode {devm devm' : Devm} {val : B256} {a : Adr}
    (h : devm.pop = Except.ok (val, devm')) : devm'.getCode a = devm.getCode a := by
  exact (Devm.pop_worldEq_of_ok h).getCode a |>.symm

lemma Devm.popToNat_worldEq_of_ok {devm devm' : Devm} {n : Nat}
    (h : devm.popToNat = .ok (n, devm')) : Devm.WorldEq devm devm' := by
  exact liftMach_worldEq_of_ok (core := Mach.popToNat) h

lemma Devm.popToNat_getCode {devm devm' : Devm} {val : ℕ} {a : Adr}
    (h : devm.popToNat = Except.ok (val, devm')) :
    devm'.getCode a = devm.getCode a := by
  exact (Devm.popToNat_worldEq_of_ok h).getCode a |>.symm

lemma Devm.popToAdr_getCode {devm devm' : Devm} {val : Adr} {a : Adr}
    (h : devm.popToAdr = Except.ok (val, devm')) :
    devm'.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getCode a |>.symm

lemma Devm.memExtends_getCode {devm : Devm} {ranges : List (ℕ × ℕ)} {a : Adr} :
    (devm.memExtends ranges).getCode a = devm.getCode a := by
  exact (liftMachPure_worldEq (Mach.memExtends · ranges) devm).getCode a |>.symm

lemma Devm.incrNonce_getCode {devm : Devm} {adr a : Adr} : (devm.incrNonce adr).getCode a = devm.getCode a := by
  dsimp [Devm.incrNonce, Devm.withState, Devm.setWorld, Devm.world, Devm.state,
    Devm.getCode, Devm.getAcct, State.incrNonce, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma addCreatedAccount_getCode {benv : Benv} {adr a : Adr} : (addCreatedAccount benv adr).state.getCode a = benv.state.getCode a := by
  rfl

lemma Benv.setStor_getCode {benv : Benv} {adr a : Adr} {stor : Stor} : (benv.setStor adr stor).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.setStor, Benv.state, State.setStor, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma Benv.incrNonce_getCode {benv : Benv} {adr a : Adr} : (benv.incrNonce adr).state.getCode a = benv.state.getCode a := by
  dsimp [Benv.incrNonce, Benv.state, State.incrNonce, State.set, State.getCode, State.get]
  split_ifs with h_if
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_erase]
      split_ifs; try rfl
      · have h3 := congrArg Acct.code h_if
        exact h3.symm
    · rw [Std.TreeMap.getD_erase]
      simp [h]
  · by_cases h : compare adr a = Ordering.eq
    · have h2 : adr = a := compare_eq_iff_eq.mp h
      subst h2
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h]

lemma ExecuteCode.depth_eq
    {msg : Msg} {evm_ exn_ ex}
    (run : ExecuteCode msg (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth = msg.depth := by
  rw [(ExecuteCode.some_inv run).1]; rfl

lemma ProcessMessage.depth_eq
    {msg : Msg} {evm_ exn_ ex}
    (run : ProcessMessage msg (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth = msg.depth :=
  RunFrame.depth_eq run

lemma ProcessCreateMessage.depth_eq
    {msg : Msg} {evm_ exn_ ex}
    (run : ProcessCreateMessage msg (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth = msg.depth :=
  RunFrame.depth_eq run

lemma GenericCall.depth_lt
    {sevm devm msgCallGas value caller currentTarget target
      shouldTransferValue isStatic inputIndex inputSize
      outputIndex outputSize code disablePrecompiles}
    {evm_ exn_ ex}
    (run : GenericCall sevm devm msgCallGas value caller currentTarget target
      shouldTransferValue isStatic inputIndex inputSize
      outputIndex outputSize code disablePrecompiles (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth < sevm.depth := by
  obtain ⟨f, rsm, hs, henter, _⟩ := XStep.Run.some_inv run
  rw [Frame.enter_run_depth henter]
  exact genericCall.step_spawn_depth hs

lemma GenericCreate.depth_lt
    {sevm devm endowment newAddress memoryIndex memorySize}
    {evm_ exn_ ex}
    (run : GenericCreate sevm devm endowment
      newAddress memoryIndex memorySize (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth < sevm.depth := by
  obtain ⟨f, rsm, hs, henter, _⟩ := XStep.Run.some_inv run
  rw [Frame.enter_run_depth henter]
  exact genericCreate.step_spawn_depth hs

lemma Xinst.depth_lt
    {sevm devm x} {evm_ exn_ ex}
    (run : Xinst.Run sevm devm x (.some ⟨evm_, exn_⟩) ex) :
    evm_.sta.depth < sevm.depth := by
  obtain ⟨f, rsm, hs, henter, _⟩ := XStep.Run.some_inv run
  rw [Frame.enter_run_depth henter]
  exact Xinst.step_spawn_depth hs

lemma chargeGas_getCode_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma Devm.push_getCode_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getCode a |>.symm

lemma Devm.popToAdr_getCode_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getCode a |>.symm

@[simp] lemma Except.bind_error {α β ε} (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = Except.error e := rfl
@[simp] lemma Except.bind_ok {α β ε} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

lemma chargeGas_getBal_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (chargeGas_worldEq_of_ok h).getBal a |>.symm

lemma Devm.push_getBal_eq {v devm devm'} (h : Devm.push v devm = .ok devm') (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) h).getBal a |>.symm

lemma Devm.popToAdr_getBal_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (liftMach_worldEq_of_ok (core := Mach.popToAdr) h).getBal a |>.symm

lemma Devm.popToNat_getBal_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  exact (Devm.popToNat_worldEq_of_ok h).getBal a |>.symm

def Devm.getStor (devm : Devm) (adr : Adr) : Stor :=
  (devm.getAcct adr).stor

lemma Devm.WorldEq.getStor {d d' : Devm} (h : Devm.WorldEq d d') (a : Adr) :
    Devm.getStor d a = Devm.getStor d' a := by
  unfold Devm.getStor Devm.getAcct
  rw [h.1]

lemma Devm.Burn.getStor {s s' : Devm} (h : Devm.Burn s s') (a : Adr) :
    Devm.getStor s' a = Devm.getStor s a := by
  simp [Devm.getStor, Devm.getAcct]; rw [h.state]

lemma Devm.PopBurn.getStor {xs} {s s' : Devm} (h : Devm.PopBurn xs s s') (a : Adr) :
    Devm.getStor s' a = Devm.getStor s a := by
  simp [Devm.getStor, Devm.getAcct]; rw [h.state]

instance : PopBurn.Inv Devm.getStor := ⟨by
  intros xs s s' h
  funext a
  exact (Devm.PopBurn.getStor h a).symm
⟩

instance : Burn.Inv Devm.getStor := ⟨by
  intros s s' h
  funext a
  exact (Devm.Burn.getStor h a).symm
⟩

lemma addAccessedStorageKey_getStor {devm : Devm} {adr : Adr} {key : B256} :
    Devm.getStor (addAccessedStorageKey devm adr key) = Devm.getStor devm := by
  funext a
  exact Devm.WorldEq.getStor (addAccessedStorageKey_worldEq devm adr key) a |>.symm

lemma Devm.pop_getStor_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor (Devm.pop_worldEq_of_ok h) a

lemma chargeGas_getStor_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor (chargeGas_worldEq_of_ok h) a

lemma Devm.push_getStor_eq {v devm devm'} (h : Devm.push v devm = .ok devm') :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor
    (liftMachExecution_worldEq_of_ok (core := Mach.push v) h) a

lemma Devm.popToAdr_getStor_eq {devm devm' adr}
    (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor (liftMach_worldEq_of_ok (core := Mach.popToAdr) h) a

lemma Devm.popToNat_getStor_eq {devm devm' n}
    (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) :
    Devm.getStor devm = Devm.getStor devm' := by
  funext a
  exact Devm.WorldEq.getStor (Devm.popToNat_worldEq_of_ok h) a

/-! ## Fieldwise `Devm.Rel` infrastructure -/

/-- Functional compatibility form of reflexivity, avoiding the deprecated root alias. -/
abbrev ReflexiveRel {α : Sort*} (r : α → α → Prop) : Prop := ∀ x, r x x

/-- Functional compatibility form of transitivity, avoiding the deprecated root alias. -/
abbrev TransitiveRel {α : Sort*} (r : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, r x y → r y z → r x z

def Devm.Rels.Refl (r : Devm.Rels) : Prop :=
  ReflexiveRel r.stack ∧ ReflexiveRel r.memory ∧ ReflexiveRel r.gasLeft ∧
  ReflexiveRel r.logs ∧ ReflexiveRel r.refundCounter ∧ ReflexiveRel r.output ∧
  ReflexiveRel r.accountsToDelete ∧ ReflexiveRel r.returnData ∧ ReflexiveRel r.error ∧
  ReflexiveRel r.accessedAddresses ∧ ReflexiveRel r.accessedStorageKeys ∧
  ReflexiveRel r.state ∧ ReflexiveRel r.createdAccounts ∧
  ReflexiveRel r.transientStorage

def Devm.Rels.Trans (r : Devm.Rels) : Prop :=
  TransitiveRel r.stack ∧ TransitiveRel r.memory ∧ TransitiveRel r.gasLeft ∧
  TransitiveRel r.logs ∧ TransitiveRel r.refundCounter ∧ TransitiveRel r.output ∧
  TransitiveRel r.accountsToDelete ∧ TransitiveRel r.returnData ∧ TransitiveRel r.error ∧
  TransitiveRel r.accessedAddresses ∧ TransitiveRel r.accessedStorageKeys ∧
  TransitiveRel r.state ∧ TransitiveRel r.createdAccounts ∧
  TransitiveRel r.transientStorage

lemma Devm.rel_refl {r : Devm.Rels} (hr : Devm.Rels.Refl r) :
    ReflexiveRel (Devm.Rel r) := by
  intro d
  rcases hr with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  constructor
  · exact h1 _
  · exact h2 _
  · exact h3 _
  · exact h4 _
  · exact h5 _
  · exact h6 _
  · exact h7 _
  · exact h8 _
  · exact h9 _
  · exact h10 _
  · exact h11 _
  · exact h12 _
  · exact h13 _
  · exact h14 _

lemma Devm.rel_trans {r : Devm.Rels} (hr : Devm.Rels.Trans r) :
    TransitiveRel (Devm.Rel r) := by
  intro a b c hab hbc
  constructor
  · exact hr.1 hab.stack hbc.stack
  · exact hr.2.1 hab.memory hbc.memory
  · exact hr.2.2.1 hab.gasLeft hbc.gasLeft
  · exact hr.2.2.2.1 hab.logs hbc.logs
  · exact hr.2.2.2.2.1 hab.refundCounter hbc.refundCounter
  · exact hr.2.2.2.2.2.1 hab.output hbc.output
  · exact hr.2.2.2.2.2.2.1 hab.accountsToDelete hbc.accountsToDelete
  · exact hr.2.2.2.2.2.2.2.1 hab.returnData hbc.returnData
  · exact hr.2.2.2.2.2.2.2.2.1 hab.error hbc.error
  · exact hr.2.2.2.2.2.2.2.2.2.1 hab.accessedAddresses hbc.accessedAddresses
  · exact hr.2.2.2.2.2.2.2.2.2.2.1 hab.accessedStorageKeys hbc.accessedStorageKeys
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.1 hab.state hbc.state
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.2.1 hab.createdAccounts hbc.createdAccounts
  · exact hr.2.2.2.2.2.2.2.2.2.2.2.2.2 hab.transientStorage hbc.transientStorage

/-! ## Outcome-aware effects for the EVM semantic layers -/

namespace Outcome

/-- Outcome-aware lifting of a state relation across both `Except` branches. -/
def Rel {σ ε α : Type}
    (errState : ε → σ) (okState : α → σ)
    (R : σ → σ → Prop) (pre : σ) : Except ε α → Prop
  | .error err => R pre (errState err)
  | .ok value => R pre (okState value)

/-
This is the generic weakening rule for both success and error outcomes.
-/
lemma Rel.mono {σ ε α : Type}
    {errState : ε → σ} {okState : α → σ} {R S : σ → σ → Prop}
    {pre : σ} {out : Except ε α}
    (hrefine : ∀ ⦃s t⦄, R s t → S s t)
    (h : Rel errState okState R pre out) :
    Rel errState okState S pre out := by
  cases out <;> exact hrefine h

end Outcome

/-- Canonical outcome-aware preservation statement for dynamic EVM execution. -/
def Execution.Rel (R : Devm → Devm → Prop) (pre : Devm) (out : Execution) : Prop :=
  Outcome.Rel Prod.snd id R pre out

lemma outcomeRel_toExecution {R : Devm → Devm → Prop} {pre : Devm}
    {out : Except (EvmError × Devm) (Unit × Devm)}
    (h : Outcome.Rel Prod.snd Prod.snd R pre out) :
    Execution.Rel R pre (Footprint.toExecution out) := by
  cases out <;> exact h

-- The full-frame infrastructure and master regular-instruction theorem are
-- declared here so that the legacy observation lemmas below can be stated as
-- projections of them.

-- Paired projection of the two deletion-relevant sets
def Devm.delSets (d : Devm) : AdrSet × AdrSet :=
  (d.accountsToDelete, d.createdAccounts)

/-! ## Full-frame relations for instruction preservation -/

/-- A Mach-only step may change exactly the three `Mach` fields. -/
def Devm.Rels.machFrame : Devm.Rels :=
  { Devm.Rels.eq with
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True }

/-- A regular instruction may change every field except the world and the two
    deletion-relevant sets. -/
def Devm.Rels.instructionFrame : Devm.Rels :=
  {
    stack := fun _ _ => True
    memory := fun _ _ => True
    gasLeft := fun _ _ => True
    logs := fun _ _ => True
    refundCounter := fun _ _ => True
    output := fun _ _ => True
    accountsToDelete := _root_.Eq
    returnData := fun _ _ => True
    error := fun _ _ => True
    accessedAddresses := fun _ _ => True
    accessedStorageKeys := fun _ _ => True
    state := _root_.Eq
    createdAccounts := _root_.Eq
    transientStorage := _root_.Eq }

abbrev Devm.MachFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.machFrame

abbrev Devm.InstructionFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.instructionFrame

/-- The part of `Meta` that an instruction-frame lift must preserve. -/
def Meta.InstructionFrame (a b : Meta) : Prop :=
  a.accountsToDelete = b.accountsToDelete ∧
    a.createdAccounts = b.createdAccounts

lemma Devm.Rels.instructionFrame_refl :
    Devm.Rels.Refl Devm.Rels.instructionFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.instructionFrame, ReflexiveRel]

lemma Devm.Rels.instructionFrame_trans :
    Devm.Rels.Trans Devm.Rels.instructionFrame := by
  simp [Devm.Rels.Trans, Devm.Rels.instructionFrame, TransitiveRel]

lemma Devm.instructionFrame_refl : ReflexiveRel Devm.InstructionFrame :=
  Devm.rel_refl Devm.Rels.instructionFrame_refl

lemma Devm.instructionFrame_trans : TransitiveRel Devm.InstructionFrame :=
  Devm.rel_trans Devm.Rels.instructionFrame_trans

lemma Devm.machFrame_refines_instructionFrame :
    ∀ ⦃d d'⦄, Devm.MachFrame d d' → Devm.InstructionFrame d d' := by
  intro d d' h
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := h.accountsToDelete
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := h.state
    createdAccounts := h.createdAccounts
    transientStorage := h.transientStorage }

lemma Devm.InstructionFrame.getBal {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getBal a = d'.getBal a := by
  unfold Devm.getBal Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.getStor {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    Devm.getStor d a = Devm.getStor d' a := by
  unfold Devm.getStor Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.getCode {d d' : Devm}
    (h : Devm.InstructionFrame d d') (a : Adr) :
    d.getCode a = d'.getCode a := by
  unfold Devm.getCode Devm.getAcct
  rw [h.state]

lemma Devm.InstructionFrame.delSets {d d' : Devm}
    (h : Devm.InstructionFrame d d') :
    Devm.delSets d = Devm.delSets d' :=
  Prod.ext h.accountsToDelete h.createdAccounts

lemma Devm.machFrame_setMach (d : Devm) (mach : Mach) :
    Devm.MachFrame d (d.setMach mach) := by
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := rfl
    refundCounter := rfl
    output := rfl
    accountsToDelete := rfl
    returnData := rfl
    error := rfl
    accessedAddresses := rfl
    accessedStorageKeys := rfl
    state := rfl
    createdAccounts := rfl
    transientStorage := rfl }

lemma Devm.instructionFrame_setMachMeta (d : Devm) (view : Mach × Meta)
    (h : Meta.InstructionFrame d.meta view.2) :
    Devm.InstructionFrame d
      { d with mach := view.1, «meta» := view.2 } := by
  rcases h with ⟨hdel, hcreated⟩
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := hdel
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := rfl
    createdAccounts := hcreated
    transientStorage := rfl }

/-! ### Full-frame lift rules -/

lemma liftMach_machFrame (core : Mach → Footprint.Outcome Mach α) (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (liftMach core d) := by
  unfold liftMach Footprint.liftOutcome
  cases core d.mach <;> exact Devm.machFrame_setMach d _

lemma liftMachPure_machFrame (core : Mach → Mach) (d : Devm) :
    Devm.MachFrame d (liftMachPure core d) := by
  exact Devm.machFrame_setMach d _

lemma liftMachExecution_machFrame
    (core : Mach → Footprint.Outcome Mach Unit) (d : Devm) :
    Execution.Rel Devm.MachFrame d (liftMachExecution core d) := by
  unfold liftMachExecution
  exact outcomeRel_toExecution (liftMach_machFrame core d)

lemma liftMachMeta_instructionFrame
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) α) (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.mach d.meta)) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d
      (liftMachMeta core d) := by
  cases h : core d.mach d.meta with
  | error e =>
      rw [h] at hcore
      simpa only [liftMachMeta, Footprint.liftOutcome, h, Outcome.Rel] using
        Devm.instructionFrame_setMachMeta d e.2 hcore
  | ok x =>
      rw [h] at hcore
      simpa only [liftMachMeta, Footprint.liftOutcome, h, Outcome.Rel] using
        Devm.instructionFrame_setMachMeta d x.2 hcore

lemma liftMachMetaPure_instructionFrame
    (core : Mach → Meta → Mach × Meta) (d : Devm)
    (hcore : Meta.InstructionFrame d.meta (core d.mach d.meta).2) :
    Devm.InstructionFrame d (liftMachMetaPure core d) := by
  exact Devm.instructionFrame_setMachMeta d _ hcore

lemma liftMachMetaExecution_instructionFrame
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit) (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.mach d.meta)) :
    Execution.Rel Devm.InstructionFrame d (liftMachMetaExecution core d) := by
  unfold liftMachMetaExecution
  exact outcomeRel_toExecution (liftMachMeta_instructionFrame core d hcore)

lemma liftMachMetaWorldExecution_instructionFrame
    (core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    (d : Devm)
    (hcore : Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame d.meta (core d.world d.mach d.meta)) :
    Execution.Rel Devm.InstructionFrame d
      (liftMachMetaWorldExecution core d) := by
  exact liftMachMetaExecution_instructionFrame (core d.world) d hcore

/-! ### Full-frame primitive facts -/

lemma Devm.pop_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.pop d) := by
  exact liftMach_machFrame Mach.pop d

lemma Devm.pop_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.pop d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.pop_machFrame d)

lemma Devm.push_machFrame (x : B256) (d : Devm) :
    Execution.Rel Devm.MachFrame d (Devm.push x d) := by
  exact liftMachExecution_machFrame (Mach.push x) d

lemma Devm.push_instructionFrame (x : B256) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (Devm.push x d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.push_machFrame x d)

lemma pushItem_machFrame (x : B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (pushItem x cost d) := by
  exact liftMachExecution_machFrame (Mach.pushItem x cost) d

lemma pushItem_instructionFrame (x : B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (pushItem x cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (pushItem_machFrame x cost d)

lemma chargeGas_machFrame (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (chargeGas cost d) := by
  exact liftMachExecution_machFrame (Mach.chargeGas cost) d

lemma chargeGas_instructionFrame (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (chargeGas cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (chargeGas_machFrame cost d)

lemma Devm.popToNat_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popToNat d) := by
  exact liftMach_machFrame Mach.popToNat d

lemma Devm.popToNat_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popToNat d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popToNat_machFrame d)

lemma Devm.popToAdr_machFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popToAdr d) := by
  exact liftMach_machFrame Mach.popToAdr d

lemma Devm.popToAdr_instructionFrame (d : Devm) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popToAdr d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popToAdr_machFrame d)

lemma Devm.popN_machFrame (d : Devm) (n : Nat) :
    Outcome.Rel Prod.snd Prod.snd Devm.MachFrame d (Devm.popN d n) := by
  exact liftMach_machFrame (Mach.popN · n) d

lemma Devm.popN_instructionFrame (d : Devm) (n : Nat) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d (Devm.popN d n) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (Devm.popN_machFrame d n)

lemma applyUnary_machFrame (f : B256 → B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyUnary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyUnary f cost) d

lemma applyUnary_instructionFrame (f : B256 → B256) (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyUnary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyUnary_machFrame f cost d)

lemma applyBinary_machFrame (f : B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyBinary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyBinary f cost) d

lemma applyBinary_instructionFrame (f : B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyBinary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyBinary_machFrame f cost d)

lemma applyTernary_machFrame (f : B256 → B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.MachFrame d (applyTernary f cost d) := by
  exact liftMachExecution_machFrame (Mach.applyTernary f cost) d

lemma applyTernary_instructionFrame (f : B256 → B256 → B256 → B256)
    (cost : Nat) (d : Devm) :
    Execution.Rel Devm.InstructionFrame d (applyTernary f cost d) := by
  exact Outcome.Rel.mono Devm.machFrame_refines_instructionFrame
    (applyTernary_machFrame f cost d)

lemma Devm.memWrite_machFrame (d : Devm) (idx : Nat) (val : Bytes) :
    Devm.MachFrame d (Devm.memWrite d idx val) := by
  exact liftMachPure_machFrame (Mach.memWrite · idx val) d

lemma Devm.memWrite_instructionFrame (d : Devm) (idx : Nat) (val : Bytes) :
    Devm.InstructionFrame d (Devm.memWrite d idx val) := by
  exact Devm.machFrame_refines_instructionFrame
    (Devm.memWrite_machFrame d idx val)

lemma Devm.memExtends_machFrame (d : Devm) (ranges : List (Nat × Nat)) :
    Devm.MachFrame d (Devm.memExtends d ranges) := by
  exact liftMachPure_machFrame (Mach.memExtends · ranges) d

lemma Devm.memExtends_instructionFrame (d : Devm)
    (ranges : List (Nat × Nat)) :
    Devm.InstructionFrame d (Devm.memExtends d ranges) := by
  exact Devm.machFrame_refines_instructionFrame
    (Devm.memExtends_machFrame d ranges)

lemma addAccessedAddress_instructionFrame (d : Devm) (a : Adr) :
    Devm.InstructionFrame d (addAccessedAddress d a) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

/-- Access-delegation resolves an EOA delegation without touching the world or
    the deletion sets, so it stays inside the instruction frame. -/
lemma accessDelegation_instructionFrame (d : Devm) (adr : Adr) :
    Devm.InstructionFrame d (accessDelegation d adr).2.2.2.2 := by
  rw [accessDelegation]
  cases getDelegatedCodeAddress (d.state.getCode adr)
  · exact Devm.instructionFrame_refl d
  · exact addAccessedAddress_instructionFrame d _

lemma addAccessedStorageKey_instructionFrame
    (d : Devm) (a : Adr) (k : B256) :
    Devm.InstructionFrame d (addAccessedStorageKey d a k) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

lemma Devm.addLog_instructionFrame (d : Devm) (log : Log) :
    Devm.InstructionFrame d (Devm.addLog d log) := by
  exact liftMachMetaPure_instructionFrame _ d ⟨rfl, rfl⟩

lemma Devm.memRead_instructionFrame (d : Devm) (index size : Nat) :
    Devm.InstructionFrame d (Devm.memRead d index size).2 := by
  unfold Devm.memRead
  split
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := rfl
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := rfl
    createdAccounts := rfl
    transientStorage := rfl }

lemma Rinst.balanceCore_meta_instructionFrame
    (world : World) (mach : Mach) (view : Meta) :
    Outcome.Rel (fun e => e.2.2) (fun x => x.2.2)
      Meta.InstructionFrame view (Rinst.balanceCore world mach view) := by
  cases hpop : mach.pop with
  | error e =>
      simp only [Rinst.balanceCore, hpop]
      exact ⟨rfl, rfl⟩
  | ok out =>
      rcases out with ⟨x, mach'⟩
      simp only [Rinst.balanceCore, hpop]
      by_cases hw : x.toAdr ∈ view.accessedAddresses
      · simp only [hw, if_pos]
        split
        · exact ⟨rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl⟩
      · simp only [hw, if_false]
        split
        · exact ⟨rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl⟩

lemma Rinst.balanceCore_instructionFrame (d : Devm) :
    Execution.Rel Devm.InstructionFrame d
      (liftMachMetaWorldExecution Rinst.balanceCore d) := by
  exact liftMachMetaWorldExecution_instructionFrame Rinst.balanceCore d
    (Rinst.balanceCore_meta_instructionFrame d.world d.mach d.meta)

/-! ### Bind composition for frame relations -/

lemma Outcome.Rel.bindExecution
    {R : Devm → Devm → Prop} (htrans : TransitiveRel R)
    {pre : Devm} {out : Except (EvmError × Devm) (α × Devm)}
    {next : α → Devm → Execution}
    (hout : Outcome.Rel Prod.snd Prod.snd R pre out)
    (hnext : ∀ x d, Execution.Rel R d (next x d)) :
    Execution.Rel R pre (out >>= fun x => next x.1 x.2) := by
  cases out with
  | error e => exact hout
  | ok x =>
      cases hn : next x.1 x.2 with
      | error e =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn, Execution.Rel, Outcome.Rel] using htrans hout h
      | ok d =>
          have h := hnext x.1 x.2
          rw [hn] at h
          simpa only [Except.bind_ok, hn, id_eq, Execution.Rel, Outcome.Rel] using htrans hout h

lemma Execution.Rel.bind
    {R : Devm → Devm → Prop} (htrans : TransitiveRel R)
    {pre : Devm} {out : Execution} {next : Devm → Execution}
    (hout : Execution.Rel R pre out)
    (hnext : ∀ d, Execution.Rel R d (next d)) :
    Execution.Rel R pre (out >>= next) := by
  cases out with
  | error e => exact hout
  | ok d =>
      cases hn : next d with
      | error e =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn, Execution.Rel, Outcome.Rel] using htrans hout h
      | ok d' =>
          have h := hnext d
          rw [hn] at h
          simpa only [Except.bind_ok, hn, id_eq, Execution.Rel, Outcome.Rel] using htrans hout h

/-! ### Step 3 calibration cases -/

lemma Rinst.balance_runCore_instructionFrame
    (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame devm
      (Rinst.runCore pc devm sevm .balance) := by
  simpa only [Rinst.runCore] using Rinst.balanceCore_instructionFrame devm

lemma Rinst.blobhash_runCore_instructionFrame
    (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame devm
      (Rinst.runCore pc devm sevm .blobhash) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame devm) (next := fun x d =>
      chargeGas gHashopcode d >>=
        Devm.push (sevm.tenvStat.blobVersionedHashes.getD x.toNat 0)) ?_
  intro x d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gHashopcode d)
  exact Devm.push_instructionFrame _

/-! ## Master regular-instruction frame theorem -/

/-- Equality of the balance/code observations of two world states.  Storage is
    deliberately absent: it is the component written by `SSTORE`. -/
def State.BalCodeEq (a b : Jaune.State) : Prop :=
  (fun adr => ((a.get adr).bal, (a.get adr).code)) =
    fun adr => ((b.get adr).bal, (b.get adr).code)

/-- Canonical precise effect of the persistent-storage writer: balances and
code are unchanged at every address. -/
lemma State.setStorVal_balCodeEq (st : Jaune.State)
    (adr : Adr) (key value : B256) :
    State.BalCodeEq st (st.setStorVal adr key value) := by
  unfold State.BalCodeEq State.setStorVal State.get State.set
  funext adr'
  dsimp
  split_ifs with h_if
  · by_cases h_cmp : compare adr adr' = Ordering.eq
    · have h : adr = adr' := compare_eq_iff_eq.mp h_cmp
      subst h
      rw [Std.TreeMap.getD_erase]
      simp
      constructor
      · simpa only using congrArg Acct.bal h_if
      · simpa only using congrArg Acct.code h_if
    · rw [Std.TreeMap.getD_erase]
      simp [h_cmp]
  · by_cases h_cmp : compare adr adr' = Ordering.eq
    · have h : adr = adr' := compare_eq_iff_eq.mp h_cmp
      subst h
      rw [Std.TreeMap.getD_insert]
      simp
    · rw [Std.TreeMap.getD_insert]
      simp [h_cmp]

/-- `SSTORE` may change storage in `state`, but preserves balances, code, and
    the other world/frame fields. -/
def Devm.Rels.stateWriteFrame : Devm.Rels :=
  { Devm.Rels.instructionFrame with state := State.BalCodeEq }

/-- `TSTORE` may change `transientStorage`, but preserves the other
    world/frame fields. -/
def Devm.Rels.transientWriteFrame : Devm.Rels :=
  { Devm.Rels.instructionFrame with transientStorage := fun _ _ => True }

abbrev Devm.StateWriteFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.stateWriteFrame

abbrev Devm.TransientWriteFrame : Devm → Devm → Prop :=
  Devm.Rel Devm.Rels.transientWriteFrame

lemma Devm.Rels.stateWriteFrame_refl :
    Devm.Rels.Refl Devm.Rels.stateWriteFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.stateWriteFrame,
    Devm.Rels.instructionFrame, State.BalCodeEq, ReflexiveRel]

lemma Devm.Rels.stateWriteFrame_trans :
    Devm.Rels.Trans Devm.Rels.stateWriteFrame := by
  simp_all [Devm.Rels.Trans, Devm.Rels.stateWriteFrame,
    Devm.Rels.instructionFrame, State.BalCodeEq, TransitiveRel]

lemma Devm.Rels.transientWriteFrame_refl :
    Devm.Rels.Refl Devm.Rels.transientWriteFrame := by
  simp [Devm.Rels.Refl, Devm.Rels.transientWriteFrame,
    Devm.Rels.instructionFrame, ReflexiveRel]

lemma Devm.Rels.transientWriteFrame_trans :
    Devm.Rels.Trans Devm.Rels.transientWriteFrame := by
  simp [Devm.Rels.Trans, Devm.Rels.transientWriteFrame,
    Devm.Rels.instructionFrame, TransitiveRel]

lemma Devm.stateWriteFrame_refl : ReflexiveRel Devm.StateWriteFrame :=
  Devm.rel_refl Devm.Rels.stateWriteFrame_refl

lemma Devm.stateWriteFrame_trans : TransitiveRel Devm.StateWriteFrame :=
  Devm.rel_trans Devm.Rels.stateWriteFrame_trans

lemma Devm.transientWriteFrame_refl : ReflexiveRel Devm.TransientWriteFrame :=
  Devm.rel_refl Devm.Rels.transientWriteFrame_refl

lemma Devm.transientWriteFrame_trans : TransitiveRel Devm.TransientWriteFrame :=
  Devm.rel_trans Devm.Rels.transientWriteFrame_trans

lemma Devm.instructionFrame_refines_stateWriteFrame :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.StateWriteFrame d d' := by
  intro d d' h
  refine { h with state := ?_ }
  change State.BalCodeEq d.state d'.state
  rw [h.state]
  rfl

lemma Devm.instructionFrame_refines_transientWriteFrame :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.TransientWriteFrame d d' := by
  intro d d' h
  exact { h with transientStorage := trivial }

lemma Devm.instructionFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (htransient : d.transientStorage = d'.transientStorage) :
    Devm.InstructionFrame d d' := by
  exact {
    stack := trivial
    memory := trivial
    gasLeft := trivial
    logs := trivial
    refundCounter := trivial
    output := trivial
    accountsToDelete := hdel
    returnData := trivial
    error := trivial
    accessedAddresses := trivial
    accessedStorageKeys := trivial
    state := hstate
    createdAccounts := hcreated
    transientStorage := htransient }

lemma popChargePush_instructionFrame (pre : Devm)
    (cost : B256 → Devm → Nat) (value : B256 → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.pop
      let d ← chargeGas (cost x d) d
      d.push (value x d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun x d =>
      chargeGas (cost x d) d >>= fun d => Devm.push (value x d) d) ?_
  intro x d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x d) d)
  intro d'
  exact Devm.push_instructionFrame (value x d') d'

lemma Execution.Rel.trans_left {R : Devm → Devm → Prop}
    (htrans : TransitiveRel R) {a b : Devm} {out : Execution}
    (hab : R a b) (hout : Execution.Rel R b out) :
    Execution.Rel R a out := by
  cases out <;> exact htrans hab hout

lemma pop2ChargePush_instructionFrame (pre : Devm)
    (cost : B256 → B256 → Devm → Nat)
    (value : B256 → B256 → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.pop
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      d.push (value x y d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      d.push (value x y d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame d) (next := fun y d =>
      chargeGas (cost x y d) d >>= fun d => Devm.push (value x y d) d) ?_
  intro y d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y d) d)
  intro d'
  exact Devm.push_instructionFrame (value x y d') d'

lemma Rinst.exp_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .exp) := by
  simpa only [Rinst.runCore] using
    (pop2ChargePush_instructionFrame pre
      (fun _ exponent _ => gExp + gExpbyte * exponent.bytecount)
      (fun base exponent _ => B256.bexp base exponent))

lemma Rinst.calldataload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .calldataload) := by
  simpa only [Rinst.runCore] using
    (popChargePush_instructionFrame pre (fun _ _ => gVerylow)
      (fun start _ => Bytes.toB256 <| sevm.data.sliceD start.toNat 32 0))

lemma Rinst.blockhash_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .blockhash) := by
  simpa only [Rinst.runCore] using
    (popChargePush_instructionFrame pre (fun _ _ => gBlockhash)
      (fun blockNumberWord _ =>
        let blockNumber := blockNumberWord.toNat
        let maxBlockNumber := blockNumber + 256
        if sevm.benvStat.number ≤ blockNumber ∨
            maxBlockNumber < sevm.benvStat.number then 0
        else sevm.benvStat.blockHashes.getD
          (sevm.benvStat.blockHashes.length -
            (sevm.benvStat.number - blockNumber)) 0))

lemma Rinst.gas_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .gas) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gBase pre)
  intro d
  exact Devm.push_instructionFrame d.gasLeft.toB256 d

/-- `CLZ` needs its own case because its body is fork-gated.

Where EIP-7939 is in force it is an ordinary unary operation; where it is not,
0x1E is an undefined byte and the instruction halts without touching the frame.
Both branches preserve the frame, so the statement is the same one every other
regular instruction satisfies and no fork hypothesis is needed. -/
lemma Rinst.clz_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .clz) := by
  simp only [Rinst.runCore]
  split
  · exact applyUnary_instructionFrame _ _ pre
  · exact Devm.instructionFrame_refl pre

lemma Rinst.tload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .tload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun key d =>
      pushItem (d.getTransVal sevm.currentTarget key) gasWarmAccess d) ?_
  intro key d
  exact pushItem_instructionFrame _ _ d

lemma popNat3ChargePure_instructionFrame (pre : Devm)
    (cost : Nat → Nat → Nat → Devm → Nat)
    (finish : Nat → Nat → Nat → Devm → Devm)
    (hfinish : ∀ x y z d, Devm.InstructionFrame d (finish x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      let d ← chargeGas (cost x y z d) d
      .ok (finish x y z d)) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun z d =>
      chargeGas (cost x y z d) d >>= fun d => .ok (finish x y z d)) ?_
  intro z d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y z d) d)
  intro d'
  exact hfinish x y z d'

lemma popNatPopChargePure_instructionFrame (pre : Devm)
    (cost : Nat → B256 → Devm → Nat)
    (finish : Nat → B256 → Devm → Devm)
    (hfinish : ∀ x y d, Devm.InstructionFrame d (finish x y d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      .ok (finish x y d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.pop
      let d ← chargeGas (cost x y d) d
      .ok (finish x y d)) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame d) (next := fun y d =>
      chargeGas (cost x y d) d >>= fun d => .ok (finish x y d)) ?_
  intro y d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (cost x y d) d)
  intro d'
  exact hfinish x y d'

lemma Rinst.calldatacopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .calldatacopy) := by
  simpa only [Rinst.runCore] using
    (popNat3ChargePure_instructionFrame pre
      (fun memoryStart _ size d =>
        gVerylow + gasCopy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart dataStart size d =>
        d.memWrite memoryStart (sevm.data.sliceD dataStart size 0))
      (fun memoryStart dataStart size d =>
        Devm.memWrite_instructionFrame d memoryStart
          (sevm.data.sliceD dataStart size 0)))

lemma Rinst.codecopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .codecopy) := by
  simpa only [Rinst.runCore] using
    (popNat3ChargePure_instructionFrame pre
      (fun memoryStart _ size d =>
        gVerylow + gasCopy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart codeStart size d => d.memWrite memoryStart
        (sevm.code.sliceD codeStart size (Linst.toUInt8 .stop)))
      (fun memoryStart codeStart size d => Devm.memWrite_instructionFrame d
        memoryStart (sevm.code.sliceD codeStart size (Linst.toUInt8 .stop))))

lemma Rinst.mstore_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mstore) := by
  simpa only [Rinst.runCore] using
    (popNatPopChargePure_instructionFrame pre
      (fun start _ d => gVerylow + d.extCost [(start, 32)])
      (fun start value d => d.memWrite start value.toBytes)
      (fun start value d =>
        Devm.memWrite_instructionFrame d start value.toBytes))

lemma Rinst.mstore8_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mstore8) := by
  simpa only [Rinst.runCore] using
    (popNatPopChargePure_instructionFrame pre
      (fun start _ d => gVerylow + d.extCost [(start, 1)])
      (fun start value d => d.memWrite start [value.2.2.toUInt8])
      (fun start value d =>
        Devm.memWrite_instructionFrame d start [value.2.2.toUInt8]))

lemma Rinst.mload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun start d =>
      chargeGas (gVerylow + d.extCost [(start, 32)]) d >>= fun d =>
        Devm.push (Bytes.toB256 (d.memRead start 32).1) (d.memRead start 32).2) ?_
  intro start d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Execution.Rel.trans_left Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' start 32)
    (Devm.push_instructionFrame _ (d'.memRead start 32).2)

lemma Rinst.kec_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .kec) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun start d => do
      let ⟨size, d⟩ ← d.popToNat
      let d ← chargeGas
        (gKeccak256 + gasKeccak256Word * ceilDiv size 32 +
          d.extCost [(start, size)]) d
      let ⟨arg, d⟩ := d.memRead start size
      d.push arg.keccak) ?_
  intro start d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun size d =>
      chargeGas
        (gKeccak256 + gasKeccak256Word * ceilDiv size 32 +
          d.extCost [(start, size)]) d >>= fun d =>
        Devm.push (d.memRead start size).1.keccak (d.memRead start size).2) ?_
  intro size d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Execution.Rel.trans_left Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' start size)
    (Devm.push_instructionFrame _ (d'.memRead start size).2)

lemma Rinst.mcopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .mcopy) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun destination d => do
      let ⟨source, d⟩ ← d.popToNat
      let ⟨length, d⟩ ← d.popToNat
      let d ← chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro destination d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun source d => do
      let ⟨length, d⟩ ← d.popToNat
      let d ← chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro source d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun length d =>
      chargeGas (gVerylow + gasCopy * ceilDiv length 32 +
        d.extCost [(source, length), (destination, length)]) d >>= fun d =>
      .ok ((d.memRead source length).2.memWrite destination
        (d.memRead source length).1)) ?_
  intro length d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  exact Devm.instructionFrame_trans
    (Devm.memRead_instructionFrame d' source length)
    (Devm.memWrite_instructionFrame (d'.memRead source length).2 destination
      (d'.memRead source length).1)

lemma popAdrAccessChargePush_instructionFrame (pre : Devm)
    (value : Adr → Devm → B256) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨a, d⟩ ← pre.popToAdr
      let d ← if a ∈ d.accessedAddresses then chargeGas gasWarmAccess d
        else chargeGas gasColdAccountAccess (addAccessedAddress d a)
      d.push (value a d)) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToAdr_instructionFrame pre) (next := fun a d => do
      let d ← if a ∈ d.accessedAddresses then chargeGas gasWarmAccess d
        else chargeGas gasColdAccountAccess (addAccessedAddress d a)
      d.push (value a d)) ?_
  intro a d
  by_cases h : a ∈ d.accessedAddresses
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame gasWarmAccess d)
    intro d'
    exact Devm.push_instructionFrame (value a d') d'
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedAddress_instructionFrame d a)
        (chargeGas_instructionFrame gasColdAccountAccess
          (addAccessedAddress d a)))
    intro d'
    exact Devm.push_instructionFrame (value a d') d'

lemma Rinst.extcodesize_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodesize) := by
  simpa only [Rinst.runCore] using
    (popAdrAccessChargePush_instructionFrame pre
      (fun a d => (d.getCode a).size.toB256))

lemma Rinst.extcodehash_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodehash) := by
  simpa only [Rinst.runCore] using
    (popAdrAccessChargePush_instructionFrame pre (fun a d =>
      let account := d.getAcct a
      if account.Empty then 0
      else ByteArray.keccak 0 account.code.size account.code))

lemma Rinst.sload_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .sload) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.pop_instructionFrame pre) (next := fun key d =>
      if (sevm.currentTarget, key) ∈ d.accessedStorageKeys then
        chargeGas gasWarmAccess d >>= fun d =>
          Devm.push (d.getStorVal sevm.currentTarget key) d
      else chargeGas gasColdSload
        (addAccessedStorageKey d sevm.currentTarget key) >>= fun d =>
          Devm.push (d.getStorVal sevm.currentTarget key) d) ?_
  intro key d
  by_cases h : (sevm.currentTarget, key) ∈ d.accessedStorageKeys
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame gasWarmAccess d)
    intro d'
    exact Devm.push_instructionFrame _ d'
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedStorageKey_instructionFrame d sevm.currentTarget key)
        (chargeGas_instructionFrame gasColdSload
          (addAccessedStorageKey d sevm.currentTarget key)))
    intro d'
    exact Devm.push_instructionFrame _ d'

lemma Rinst.pop_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .pop) := by
  simp only [Rinst.runCore]
  have hp := Devm.pop_instructionFrame pre
  cases h : pre.pop with
  | error e =>
      rw [h] at hp
      exact hp
  | ok x =>
      rcases x with ⟨word, d⟩
      rw [h] at hp
      simpa [h] using
        (Execution.Rel.trans_left Devm.instructionFrame_trans hp
          (chargeGas_instructionFrame gBase d))

lemma Rinst.dup_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 16) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.dup n)) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gVerylow pre)
  intro d
  cases h : d.stack[n]? with
  | none =>
      simp only
      exact Devm.instructionFrame_refl d
  | some word =>
      simp only
      exact Devm.push_instructionFrame word d

lemma Rinst.swap_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 16) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.swap n)) := by
  simp only [Rinst.runCore]
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame gVerylow pre)
  intro d
  cases h : d.stack.swap n with
  | none =>
      simp only
      exact Devm.instructionFrame_refl d
  | some stack =>
      simp only
      exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma popNat3Bind_instructionFrame (pre : Devm)
    (next : Nat → Nat → Nat → Devm → Execution)
    (hnext : ∀ x y z d, Execution.Rel Devm.InstructionFrame d
      (next x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      next x y z d) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := next x y) ?_
  exact hnext x y

lemma popAdrNat3Bind_instructionFrame (pre : Devm)
    (next : Adr → Nat → Nat → Nat → Devm → Execution)
    (hnext : ∀ a x y z d, Execution.Rel Devm.InstructionFrame d
      (next a x y z d)) :
    Execution.Rel Devm.InstructionFrame pre (do
      let ⟨a, d⟩ ← pre.popToAdr
      let ⟨x, d⟩ ← d.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) := by
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToAdr_instructionFrame pre) (next := fun a d => do
      let ⟨x, d⟩ ← d.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro a d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun x d => do
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro x d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun y d => do
      let ⟨z, d⟩ ← d.popToNat
      next a x y z d) ?_
  intro y d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := next a x y) ?_
  exact hnext a x y

lemma Rinst.retdatacopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .retdatacopy) := by
  simp only [Rinst.runCore]
  refine popNat3Bind_instructionFrame pre (next := fun memoryStart returnStart size d => do
    let d ← chargeGas
      (gVerylow + gReturnDataCopy * ceilDiv size 32 +
        d.extCost [(memoryStart, size)]) d
    if d.returnData.length < returnStart + size then
      .error ⟨.halt (.outOfBoundsRead .none), d⟩
    let value := d.returnData.sliceD returnStart size 0
    .ok (d.withMemory (d.memory.write memoryStart value))) ?_
  intro memoryStart returnStart size d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame
      (gVerylow + gReturnDataCopy * ceilDiv size 32 +
        d.extCost [(memoryStart, size)]) d)
  intro d'
  by_cases h : d'.returnData.length < returnStart + size
  · simp only [h, if_pos]
    exact Devm.instructionFrame_refl d'
  · simp only [h, if_false]
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma Rinst.extcodecopy_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm .extcodecopy) := by
  simp only [Rinst.runCore]
  refine popAdrNat3Bind_instructionFrame pre
    (next := fun a memoryStart codeStart size d =>
      if a ∈ d.accessedAddresses then do
        let d ← chargeGas (gasWarmAccess + gasCopy * ceilDiv size 32 +
          d.extCost [(memoryStart, size)]) d
        let value := (d.getCode a).sliceD codeStart size (Linst.toUInt8 .stop)
        .ok (d.withMemory (d.memory.write memoryStart value))
      else do
        let d ← chargeGas
          (gasColdAccountAccess + gasCopy * ceilDiv size 32 +
            d.extCost [(memoryStart, size)]) (addAccessedAddress d a)
        let value := (d.getCode a).sliceD codeStart size (Linst.toUInt8 .stop)
        .ok (d.withMemory (d.memory.write memoryStart value))) ?_
  intro a memoryStart codeStart size d
  by_cases h : a ∈ d.accessedAddresses
  · simp only [h, if_pos]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame
        (gasWarmAccess + gasCopy * ceilDiv size 32 +
          d.extCost [(memoryStart, size)]) d)
    intro d'
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl
  · simp only [h, if_false]
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (Execution.Rel.trans_left Devm.instructionFrame_trans
        (addAccessedAddress_instructionFrame d a)
        (chargeGas_instructionFrame
          (gasColdAccountAccess + gasCopy * ceilDiv size 32 +
            d.extCost [(memoryStart, size)])
          (addAccessedAddress d a)))
    intro d'
    exact Devm.instructionFrame_of_world_eq rfl rfl rfl rfl

lemma Rinst.log_runCore_instructionFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) (n : Fin 5) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm (.log n)) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame pre) (next := fun memoryStart d => do
      let ⟨size, d⟩ ← d.popToNat
      let ⟨topics, d⟩ ← d.popN n
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro memoryStart d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popToNat_instructionFrame d) (next := fun size d => do
      let ⟨topics, d⟩ ← d.popN n
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro size d
  refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
    (Devm.popN_instructionFrame d n) (next := fun topics d => do
      let d ← chargeGas
        (gLog + gLogdata * size + gLogtopic * n +
          d.extCost [(memoryStart, size)]) d
      assertDynamic sevm d
      let ⟨data, d⟩ := d.memRead memoryStart size
      .ok (d.addLog ⟨sevm.currentTarget, topics, data⟩)) ?_
  intro topics d
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame _ d)
  intro d'
  unfold assertDynamic Except.assert
  split
  · exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' memoryStart size)
      (Devm.addLog_instructionFrame (d'.memRead memoryStart size).2
        ⟨sevm.currentTarget, topics, (d'.memRead memoryStart size).1⟩)
  · exact Devm.instructionFrame_refl d'

theorem Rinst.runCore_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (r : Rinst)
    (h_not_sstore : r ≠ .sstore) (h_not_tstore : r ≠ .tstore) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.runCore pc pre sevm r) := by
  cases r
  all_goals try contradiction
  all_goals try (
    with_reducible first
      | exact Rinst.exp_runCore_instructionFrame pc pre sevm
      | exact Rinst.kec_runCore_instructionFrame pc pre sevm
      | exact Rinst.balance_runCore_instructionFrame pc pre sevm
      | exact Rinst.blobhash_runCore_instructionFrame pc pre sevm
      | exact Rinst.calldataload_runCore_instructionFrame pc pre sevm
      | exact Rinst.calldatacopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.codecopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodesize_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodecopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.retdatacopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.extcodehash_runCore_instructionFrame pc pre sevm
      | exact Rinst.blockhash_runCore_instructionFrame pc pre sevm
      | exact Rinst.pop_runCore_instructionFrame pc pre sevm
      | exact Rinst.mload_runCore_instructionFrame pc pre sevm
      | exact Rinst.mstore_runCore_instructionFrame pc pre sevm
      | exact Rinst.mstore8_runCore_instructionFrame pc pre sevm
      | exact Rinst.sload_runCore_instructionFrame pc pre sevm
      | exact Rinst.tload_runCore_instructionFrame pc pre sevm
      | exact Rinst.mcopy_runCore_instructionFrame pc pre sevm
      | exact Rinst.gas_runCore_instructionFrame pc pre sevm
      | exact Rinst.clz_runCore_instructionFrame pc pre sevm
      | exact Rinst.dup_runCore_instructionFrame pc pre sevm _
      | exact Rinst.swap_runCore_instructionFrame pc pre sevm _
      | exact Rinst.log_runCore_instructionFrame pc pre sevm _)
  all_goals simp only [Rinst.runCore]
  all_goals with_reducible first
    | exact applyBinary_instructionFrame _ _ pre
    | exact applyTernary_instructionFrame _ _ pre
    | exact applyUnary_instructionFrame _ _ pre
    | exact pushItem_instructionFrame _ _ pre

lemma Devm.stateWriteFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts)
    (htransient : d.transientStorage = d'.transientStorage) :
    Devm.StateWriteFrame d d' := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := hdel
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := by
      change State.BalCodeEq d.state d'.state
      rw [hstate]
      rfl
    createdAccounts := hcreated, transientStorage := htransient }

/-- The state-writer frame implies the pre-existing `SSTORE` balance fact. -/
lemma Devm.StateWriteFrame.getBal_eq {d d' : Devm}
    (h : Devm.StateWriteFrame d d') (adr : Adr) :
    d.getBal adr = d'.getBal adr := by
  have hstate : State.BalCodeEq d.state d'.state := h.state
  unfold State.BalCodeEq at hstate
  exact congrArg Prod.fst (congrFun hstate adr)

/-- The state-writer frame implies the pre-existing `SSTORE` code fact. -/
lemma Devm.StateWriteFrame.getCode_eq {d d' : Devm}
    (h : Devm.StateWriteFrame d d') (adr : Adr) :
    d.getCode adr = d'.getCode adr := by
  have hstate : State.BalCodeEq d.state d'.state := h.state
  unfold State.BalCodeEq at hstate
  exact congrArg Prod.snd (congrFun hstate adr)

lemma Devm.setStorVal_stateWriteFrame (d : Devm)
    (adr : Adr) (key value : B256) :
    Devm.StateWriteFrame d (d.setStorVal adr key value) := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := rfl
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := by
      change State.BalCodeEq d.state (d.state.setStorVal adr key value)
      exact State.setStorVal_balCodeEq d.state adr key value
    createdAccounts := rfl, transientStorage := rfl }

lemma Devm.transientWriteFrame_of_world_eq {d d' : Devm}
    (hdel : d.accountsToDelete = d'.accountsToDelete)
    (hstate : d.state = d'.state)
    (hcreated : d.createdAccounts = d'.createdAccounts) :
    Devm.TransientWriteFrame d d' := by
  exact {
    stack := trivial, memory := trivial, gasLeft := trivial, logs := trivial
    refundCounter := trivial, output := trivial, accountsToDelete := hdel
    returnData := trivial, error := trivial, accessedAddresses := trivial
    accessedStorageKeys := trivial, state := hstate
    createdAccounts := hcreated, transientStorage := trivial }

lemma Rinst.tstore_runCore_transientWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.TransientWriteFrame pre
      (Rinst.runCore pc pre sevm .tstore) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (Devm.pop_instructionFrame pre)) (next := fun key d => do
        let ⟨value, d⟩ ← d.pop
        let d ← chargeGas gasWarmAccess d
        assertDynamic sevm d
        .ok (d.setTransVal sevm.currentTarget key value)) ?_
  intro key d
  refine Outcome.Rel.bindExecution Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (Devm.pop_instructionFrame d)) (next := fun value d => do
        let d ← chargeGas gasWarmAccess d
        assertDynamic sevm d
        .ok (d.setTransVal sevm.currentTarget key value)) ?_
  intro value d
  apply Execution.Rel.bind Devm.transientWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_transientWriteFrame
      (chargeGas_instructionFrame gasWarmAccess d))
  intro d'
  unfold assertDynamic Except.assert
  split
  · exact Devm.transientWriteFrame_of_world_eq rfl rfl rfl
  · exact Devm.transientWriteFrame_refl d'

lemma Rinst.sstore_runCore_stateWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.StateWriteFrame pre
      (Rinst.runCore pc pre sevm .sstore) := by
  simp only [Rinst.runCore]
  refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
      (Devm.pop_instructionFrame pre)) (next := fun key d => do
        let ⟨value, d⟩ ← d.pop
        .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
        let ct := sevm.currentTarget
        let original := getOrigStorVal sevm ct key
        let current := d.getStorVal ct key
        let ⟨d3, gas2⟩ ← .ok <|
          if ⟨ct, key⟩ ∉ d.accessedStorageKeys then
            (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
        let gas3 ← .ok <|
          if original = current ∧ current ≠ value then
            if original = 0 then gas2 + gasStorageSet
            else gas2 + (gasStorageUpdate - gasColdSload)
          else gas2 + gasWarmAccess
        let d4 ← .ok <| d3.withRefundCounter
          (sstoreNewRefundCounter value original current d3.refundCounter)
        let d5 ← chargeGas gas3 d4
        assertDynamic sevm d5
        .ok (d5.setStorVal ct key value)) ?_
  intro key d
  refine Outcome.Rel.bindExecution Devm.stateWriteFrame_trans
    (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
      (Devm.pop_instructionFrame d)) (next := fun value d => do
        .assert (gCallStipend < d.gasLeft) ⟨.halt (.outOfGas .none), d⟩
        let ct := sevm.currentTarget
        let original := getOrigStorVal sevm ct key
        let current := d.getStorVal ct key
        let ⟨d3, gas2⟩ ← .ok <|
          if ⟨ct, key⟩ ∉ d.accessedStorageKeys then
            (addAccessedStorageKey d ct key, gasColdSload) else (d, 0)
        let gas3 ← .ok <|
          if original = current ∧ current ≠ value then
            if original = 0 then gas2 + gasStorageSet
            else gas2 + (gasStorageUpdate - gasColdSload)
          else gas2 + gasWarmAccess
        let d4 ← .ok <| d3.withRefundCounter
          (sstoreNewRefundCounter value original current d3.refundCounter)
        let d5 ← chargeGas gas3 d4
        assertDynamic sevm d5
        .ok (d5.setStorVal ct key value)) ?_
  intro value d
  unfold Except.assert
  dsimp only
  split
  · simp only [Except.bind_ok]
    let d3gas : Devm × Nat :=
      if (sevm.currentTarget, key) ∉ d.accessedStorageKeys then
        (addAccessedStorageKey d sevm.currentTarget key, gasColdSload)
      else (d, 0)
    let gas3 :=
      if getOrigStorVal sevm sevm.currentTarget key =
          d.getStorVal sevm.currentTarget key ∧
          d.getStorVal sevm.currentTarget key ≠ value then
        if getOrigStorVal sevm sevm.currentTarget key = 0 then
          d3gas.2 + gasStorageSet
        else d3gas.2 + (gasStorageUpdate - gasColdSload)
      else d3gas.2 + gasWarmAccess
    let d4 : Devm := d3gas.1.withRefundCounter (
      sstoreNewRefundCounter value
        (getOrigStorVal sevm sevm.currentTarget key)
        (d.getStorVal sevm.currentTarget key) d3gas.1.refundCounter)
    change Execution.Rel Devm.StateWriteFrame d
      (chargeGas gas3 d4 >>= fun d5 =>
        assertDynamic sevm d5 >>= fun _ =>
          .ok (d5.setStorVal sevm.currentTarget key value))
    have hd4 : Devm.StateWriteFrame d d4 := by
      unfold d4 d3gas
      split <;> exact Devm.stateWriteFrame_of_world_eq rfl rfl rfl rfl
    apply Execution.Rel.bind Devm.stateWriteFrame_trans
      (Execution.Rel.trans_left Devm.stateWriteFrame_trans hd4
        (Outcome.Rel.mono Devm.instructionFrame_refines_stateWriteFrame
          (chargeGas_instructionFrame gas3 d4)))
    intro d5
    unfold assertDynamic Except.assert
    split
    · exact Devm.setStorVal_stateWriteFrame d5 sevm.currentTarget key value
    · exact Devm.stateWriteFrame_refl d5
  · exact Devm.stateWriteFrame_refl d

theorem Rinst.run_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (r : Rinst)
    (h_not_sstore : r ≠ .sstore) (h_not_tstore : r ≠ .tstore) :
    Execution.Rel Devm.InstructionFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ r) := by
  exact Rinst.runCore_instructionFrame pc sevm pre r
    h_not_sstore h_not_tstore

lemma Rinst.sstore_run_stateWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.StateWriteFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ .sstore) := by
  exact Rinst.sstore_runCore_stateWriteFrame pc pre sevm

lemma Rinst.tstore_run_transientWriteFrame
    (pc : Nat) (pre : Devm) (sevm : Sevm) :
    Execution.Rel Devm.TransientWriteFrame pre
      (Rinst.run ⟨pc, sevm, pre⟩ .tstore) := by
  exact Rinst.tstore_runCore_transientWriteFrame pc pre sevm

theorem Jinst.runCore_instructionFrame
    (pc : Nat) (sevm : Sevm) (pre : Devm) (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame pre
      (Jinst.runCore pc pre sevm j) := by
  cases j <;> simp only [Jinst.runCore]
  case jump =>
    cases hp : pre.pop <;> simp only [Except.bind_error, Except.bind_ok]
    · have h := Devm.pop_instructionFrame pre
      rw [hp] at h
      exact h
    · rename_i x
      rcases x with ⟨dest, d⟩
      cases hg : chargeGas gMid d <;>
          simp only [Except.bind_error, Except.bind_ok]
      · exact Devm.instructionFrame_trans
          (by have h := Devm.pop_instructionFrame pre; rw [hp] at h; exact h)
          (by have h := chargeGas_instructionFrame gMid d; rw [hg] at h; exact h)
      · unfold Except.assert
        split <;> exact Devm.instructionFrame_trans
          (by have h := Devm.pop_instructionFrame pre; rw [hp] at h; exact h)
          (by have h := chargeGas_instructionFrame gMid d; rw [hg] at h; exact h)
  case jumpi =>
    cases hp1 : pre.pop <;> simp only [Except.bind_error, Except.bind_ok]
    · have h := Devm.pop_instructionFrame pre
      rw [hp1] at h
      exact h
    · rename_i x
      rcases x with ⟨dest, d1⟩
      have h1 := Devm.pop_instructionFrame pre
      rw [hp1] at h1
      cases hp2 : d1.pop <;> simp only [Except.bind_error, Except.bind_ok]
      · have h2 := Devm.pop_instructionFrame d1
        rw [hp2] at h2
        exact Devm.instructionFrame_trans h1 h2
      · rename_i y
        rcases y with ⟨cond, d2⟩
        have h2 := Devm.pop_instructionFrame d1
        rw [hp2] at h2
        have h12 := Devm.instructionFrame_trans h1 h2
        cases hg : chargeGas gHigh d2 <;>
            simp only [Except.bind_error, Except.bind_ok]
        · have h3 := chargeGas_instructionFrame gHigh d2
          rw [hg] at h3
          exact Devm.instructionFrame_trans h12 h3
        · rename_i d3
          have h3 := chargeGas_instructionFrame gHigh d2
          rw [hg] at h3
          have h123 := Devm.instructionFrame_trans h12 h3
          split
          · exact h123
          · unfold Except.assert
            split <;> exact h123
  case jumpdest =>
    cases hg : chargeGas gJumpdest pre <;>
        simp only [Except.bind_error, Except.bind_ok]
    · have h := chargeGas_instructionFrame gJumpdest pre
      rw [hg] at h
      exact h
    · have h := chargeGas_instructionFrame gJumpdest pre
      rw [hg] at h
      exact h

theorem Jinst.run_instructionFrame (evm : Evm) (j : Jinst) :
    Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame evm.dyna
      (Jinst.run evm j) := by
  exact Jinst.runCore_instructionFrame evm.pc evm.sta evm.dyna j

theorem Linst.run_instructionFrame
    (sevm : Sevm) (pre : Devm) (l : Linst) (h_not_dest : l ≠ .dest) :
    Execution.Rel Devm.InstructionFrame pre (Linst.run sevm pre l) := by
  cases l <;> simp only [Linst.run]
  case stop => exact Devm.instructionFrame_refl pre
  case ret =>
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame pre)
      (next := fun index d => do
        let ⟨size, d⟩ ← d.popToNat
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .ok (d.withOutput output)) ?_
    intro index d
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame d)
      (next := fun size d => do
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .ok (d.withOutput output)) ?_
    intro size d
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame (d.extCost [(index, size)]) d)
    intro d'
    exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' index size)
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  case rev =>
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame pre)
      (next := fun index d => do
        let ⟨size, d⟩ ← d.popToNat
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .error (.revert, d.withOutput output)) ?_
    intro index d
    refine Outcome.Rel.bindExecution Devm.instructionFrame_trans
      (Devm.popToNat_instructionFrame d)
      (next := fun size d => do
        let d ← chargeGas (d.extCost [(index, size)]) d
        let ⟨output, d⟩ := d.memRead index size
        .error (.revert, d.withOutput output)) ?_
    intro size d
    apply Execution.Rel.bind Devm.instructionFrame_trans
      (chargeGas_instructionFrame (d.extCost [(index, size)]) d)
    intro d'
    exact Devm.instructionFrame_trans
      (Devm.memRead_instructionFrame d' index size)
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  case dest => contradiction

lemma Rinst.preserves_getCode
    {pc sevm devm r devm'}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .ok devm') (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (hf.getCode_eq a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    simpa only [Devm.getCode, Devm.getAcct, id_eq] using congrFun (congrArg (fun s => fun a => (s.get a).code) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (hf.getCode a).symm

def Execution.getCode : Execution → Adr → ByteArray
  | Except.error ⟨_, devm⟩, adr => devm.getCode adr
  | Except.ok devm, adr => devm.getCode adr

lemma chargeGas_getCode_gen {cost devm exn} (h : chargeGas cost devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  cases exn with
  | error err => exact (chargeGas_worldEq_of_error h).getCode a |>.symm
  | ok devm' => exact (chargeGas_worldEq_of_ok h).getCode a |>.symm

lemma processCreateMessage.chargeCodeGas_getCode_gen {rules : ForkRules}
    {evm : Devm} {exn : Execution}
    (h : processCreateMessage.chargeCodeGas rules evm = exn) (a : Adr) :
    Execution.getCode exn a = evm.getCode a := by
  simp only [processCreateMessage.chargeCodeGas] at h
  split at h
  · subst h; rfl
  · dsimp [Bind.bind, Except.bind] at h
    split at h
    · rename_i eq_err; subst h
      have h_charge := chargeGas_getCode_gen eq_err a
      exact h_charge
    · rename_i eq_ok; split at h
      · subst h
        have h_charge := chargeGas_getCode_eq eq_ok a
        exact h_charge
      · subst h
        have h_charge := chargeGas_getCode_eq eq_ok a
        exact h_charge

lemma Devm.push_getCode_gen {v devm} {exn : Execution} (h : Devm.push v devm = exn) (a : Adr) : Execution.getCode exn a = devm.getCode a := by
  subst h
  cases hp : Devm.push v devm with
  | error err =>
    exact (liftMachExecution_worldEq_of_error (core := Mach.push v) hp).getCode a |>.symm
  | ok d =>
    exact (liftMachExecution_worldEq_of_ok (core := Mach.push v) hp).getCode a |>.symm

def Xlot.InvGetCode : Xlot → Prop
  | .none => True
  | .some ⟨evm, exn⟩ =>
    ∀ adr,
      (evm.dyna.getCode adr).toList ≠ [] →
      evm.dyna.getCode adr = Execution.getCode exn adr

lemma applyPrecompResult_getCode (evm : Evm) (res : PrecompResult) (ex : Execution)
    (h_ex : applyPrecompResult evm res = ex) (a : Adr) :
    Execution.getCode ex a = evm.dyna.getCode a := by
  revert h_ex
  cases res <;> (intro h_ex; subst h_ex; rfl)

lemma executePrecomp_preserves_getCode (evm : Evm) (adr : Adr) (ex : Execution)
    (h_ex : executePrecomp evm adr = ex) (a : Adr) :
    Execution.getCode ex a = evm.dyna.getCode a := by
  apply applyPrecompResult_getCode evm (precompileRun evm adr) ex h_ex a

def MsgResult.getCode (exn : Except (EvmError × State × AdrSet × Tra) Devm) (a : Adr) : ByteArray :=
  match exn with
  | .ok d => d.getCode a
  | .error ⟨_, state, _, _⟩ => state.getCode a

/-! ## Step 7.2 — message-level code-effect masters

Relational code-preservation over message results.  `CodePreserve` says every
nonempty-code address is left untouched; `CodePreserveExcept w` weakens that by
also excluding the single write target `w` (the freshly-created contract). -/

def MsgResult.CodePreserve (base : State)
    (exn : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a : Adr, (base.getCode a).toList ≠ [] → MsgResult.getCode exn a = base.getCode a

def MsgResult.CodePreserveExcept (base : State) (w : Adr)
    (exn : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  ∀ a : Adr, a ≠ w → (base.getCode a).toList ≠ [] →
    MsgResult.getCode exn a = base.getCode a

/-- Relational code-preservation over an `Execution` outcome (used by the
Step 7.3 generic-operation masters): every nonempty-code address of `base` has
the same code in the result, on both the ok and error branches. -/
def Execution.CodePreserve (base : Devm) (exn : Execution) : Prop :=
  ∀ a : Adr, (base.getCode a).toList ≠ [] → Execution.getCode exn a = base.getCode a

/-- Writer leaf: `handleError` reshuffles error payloads into ok results and
selects states, but never installs new code. -/
lemma executeCode.handleError_getCode (exn : Execution) (a : Adr) :
    MsgResult.getCode (executeCode.handleError exn) a = Execution.getCode exn a := by
  cases exn with
  | ok d => rfl
  | error p =>
    rcases p with ⟨err, evm⟩
    cases err <;> rfl

/-- Writer leaf: rollback installs the selected state, so its code map is that
state's code map. -/
lemma Devm.rollback_getCode (devm : Devm) (st : State) (tra : Tra) (a : Adr) :
    (devm.rollback st tra).getCode a = st.getCode a := rfl

/-- Writer leaf: value transfer changes balances but preserves code. -/
lemma benvAfterTransfer_ok_getCode {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) (a : Adr) :
    benv.state.getCode a = msg.benv.state.getCode a := by
  dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h
  split at h
  · cases h_sub : msg.benv.subBal msg.caller msg.value with
    | none => simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h
    | some benv_sub =>
      simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h
      subst benv
      rw [Benv.addBal_getCode]
      exact Benv.subBal_getCode h_sub
  · simp only [Except.ok.injEq] at h; subst benv; rfl

/-- Writer leaf: create preparation (nonce bump, created-account marking, empty
storage) preserves code. -/
lemma processCreateMessage.msg_getCode (msg : Msg) (a : Adr) :
    (processCreateMessage.msg msg).benv.state.getCode a = msg.benv.state.getCode a := by
  dsimp [processCreateMessage.msg, Msg.withBenv]
  rw [Benv.incrNonce_getCode, addCreatedAccount_getCode, Benv.setStor_getCode]

/-- Master: `executeCode` preserves the code of every nonempty-code address.
The suspended child's oracle invariant (`inv`) supplies the interpreted-code
case; `handleError_getCode` covers precompile and error selection. -/
lemma ExecuteCode.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ExecuteCode msg xl exn) :
    MsgResult.CodePreserve msg.benv.state exn := by
  intro a ha
  unfold ExecuteCode at run
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at run
  · rcases run with ⟨raw, h_xl, h_err⟩
    subst h_err
    rw [executeCode.handleError_getCode]
    rw [h_xl] at inv
    dsimp [Xlot.InvGetCode] at inv
    rw [executeCode.enter_inl henter] at inv
    exact (inv a ha).symm
  · rcases run with ⟨h_xl, h_err⟩
    subst h_err
    rw [executeCode.handleError_getCode]
    obtain ⟨adr, hraw⟩ := executeCode.enter_inr henter
    rw [hraw]
    exact executePrecomp_preserves_getCode (initEvm msg) adr _ rfl a

lemma ProcessMessage.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessMessage msg xl exn) :
    MsgResult.CodePreserve msg.benv.state exn := by
  intro a ha
  obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at hbody
  rcases h_benv : msg.benvAfterTransfer with e | benv <;> rw [h_benv] at hbody
  · rw [hbody.2]
    dsimp [MsgResult.getCode, processMessage.settle]
    dsimp [Msg.benvAfterTransfer, Msg.shouldTransferValue] at h_benv
    split at h_benv
    · cases h_sub : msg.benv.subBal msg.caller msg.value
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
        subst h_benv
        rfl
      · simp [h_sub, Option.toExcept, Bind.bind, Except.bind] at h_benv
    · contradiction
  · have h_benv_code := benvAfterTransfer_ok_getCode h_benv a
    have ha' : ( (msg.withBenv benv).benv.state.getCode a ).toList ≠ [] := by
      dsimp [Msg.withBenv]
      rw [h_benv_code]
      exact ha
    have h_exec_cond := ExecuteCode.codePreserve inv hbody a ha'
    dsimp [Msg.withBenv] at h_exec_cond
    rw [h_benv_code] at h_exec_cond
    unfold processMessage.settle
    rcases r0 with e' | evm
    · exact h_exec_cond
    · dsimp only [bind, Except.bind]
      split
      · exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a
      · exact h_exec_cond

lemma ProcessMessage.preserves_getCode_gen
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessMessage msg xl exn) :
    ∀ a : Adr,
      (msg.benv.state.getCode a).toList ≠ [] →
      MsgResult.getCode exn a = msg.benv.state.getCode a :=
  ProcessMessage.codePreserve inv run

lemma setCode_getCode {evm : Devm} {a b : Adr} {code : ByteArray} (h : a ≠ b) :
  (evm.setCode a code).getCode b = evm.getCode b := by
  dsimp [Devm.setCode, Devm.withState, Devm.setWorld, Devm.world,
    Devm.getCode, Devm.state, Devm.getAcct, State.setCode, State.set,
    State.getCode, State.get]
  split_ifs with h_if
  · by_cases hc : compare a b = Ordering.eq
    · exact False.elim (h (compare_eq_iff_eq.mp hc))
    · rw [Std.TreeMap.getD_erase]
      simp [hc]
  · by_cases hc : compare a b = Ordering.eq
    · exact False.elim (h (compare_eq_iff_eq.mp hc))
    · rw [Std.TreeMap.getD_insert]
      simp [hc]

/-- Master: `processCreateMessage` preserves the code of every nonempty-code
address *other than* the create target.  Create preparation
(`processCreateMessage.msg_getCode`) and the interpreted body
(`ProcessMessage.codePreserve`) preserve code; code-gas charging preserves it
(`chargeCodeGas_getCode_gen`); create completion writes only `msg.currentTarget`
through `setCode` (`setCode_getCode`, excluded by `a ≠ msg.currentTarget`); the
halt/error paths select states via rollback (`Devm.rollback_getCode`). -/
lemma ProcessCreateMessage.codePreserve
    {msg : Msg} {xl : Xlot} {exn : Except (EvmError × State × AdrSet × Tra) Devm}
    (inv : xl.InvGetCode)
    (run : ProcessCreateMessage msg xl exn) :
    MsgResult.CodePreserveExcept msg.benv.state msg.currentTarget exn := by
  intro a h_a ha
  have h_benv_code := processCreateMessage.msg_getCode msg a
  have ha' : ((processCreateMessage.msg msg).benv.state.getCode a).toList ≠ [] := by
    rw [h_benv_code]; exact ha
  obtain ⟨ex', h_exec, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have h_exec_cond := ProcessMessage.codePreserve inv h_exec a ha'
  rw [h_benv_code] at h_exec_cond
  unfold processCreateMessage.settle
  rcases ex' with x | evm
  · exact h_exec_cond
  · dsimp only [bind, Except.bind]
    split
    · rename_i h_none
      cases h_charge : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | error err =>
        rcases err with ⟨err_msg, err_evm⟩
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        change err_evm.state.getCode a = evm.state.getCode a at h_getCode
        cases err_msg <;>
          simp only [MsgResult.getCode, processCreateMessage.exceptionalHalt] <;>
          first
            | rfl
            | (rw [h_getCode]; exact h_exec_cond)
      | ok devm_charge =>
        dsimp only [MsgResult.getCode]
        have h_getCode := processCreateMessage.chargeCodeGas_getCode_gen h_charge a
        dsimp [Execution.getCode] at h_getCode
        rw [setCode_getCode h_a.symm]
        rw [h_getCode]
        exact h_exec_cond
    · rename_i h_some
      exact Devm.rollback_getCode evm msg.benv.state msg.tenv.transientStorage a

lemma createMsg_benv_state_getCode
    {sevm : Sevm} {devm : Devm} {createGas : Nat} {endowment : B256}
    {newAddress : Adr} {calldata : Bytes} (a : Adr) :
    (createMsg sevm devm createGas endowment newAddress calldata).benv.state.getCode a
      = devm.getCode a := rfl

/-- The CREATE-family return path preserves code at every address other than
the freshly created one, given the child frame preserved it. -/
lemma Resume.create_getCode {parent : Devm} {newAddress a : Adr}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a) :
    Execution.getCode ((Resume.create parent newAddress).run r) a =
      parent.getCode a := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind]
  · dsimp only [MsgResult.getCode] at h
    dsimp only [Execution.getCode]
    change state.getCode a = parent.getCode a
    exact h
  · dsimp only [MsgResult.getCode] at h
    split
    · rw [Devm.push_getCode_gen rfl a]
      dsimp only [incorporateChildOnError]
      exact h
    · rw [Devm.push_getCode_gen rfl a]
      dsimp only [incorporateChildOnSuccess]
      exact h

lemma GenericCreate.codePreserve
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : Nat} {xl : Xlot} {exn : Execution} (inv : xl.InvGetCode)
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl exn) :
    Execution.CodePreserve devm exn := by
  intro a ha
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- init-code-size assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    rfl
  -- static-context assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    rfl
  -- balance / max-nonce / depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- address-collision early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  -- address-collision early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    rename_i h_collision
    have h_parent : ∀ b : Adr,
        (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode b = devm.getCode b := by
      intro b
      rw [addAccessedAddress_getCode]
      exact Devm.incrNonce_getCode
    have h_a_ne : a ≠ newAddress := by
      intro h_eq
      push Not at h_collision
      have h_code_size : ((addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode newAddress).size = 0 :=
        h_collision.2.1
      have h_empty : devm.getCode newAddress = .empty := by
        rw [← h_parent newAddress]
        cases h_code' : (addAccessedAddress
          (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).getCode newAddress with
        | mk data =>
          rw [h_code'] at h_code_size
          cases data with
          | mk l =>
            cases l
            · rfl
            · contradiction
      rw [h_eq, h_empty] at ha
      exact ha (by unfold ByteArray.toList ByteArray.toList.loop; rfl)
    rw [Resume.create_getCode ?_, h_parent a]
    exact ProcessCreateMessage.codePreserve inv hframe a h_a_ne
      (by rw [createMsg_benv_state_getCode, h_parent a]; exact ha)

lemma callMsg_benv_state_getCode
    {sevm : Sevm} {evm1 : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {calldata : Bytes} {code : ByteArray} {disablePrecompiles : Bool} (a : Adr) :
    ( callMsg sevm evm1 gas value caller target codeAddress shouldTransferValue
        isStaticcall calldata code disablePrecompiles ).benv.state.getCode a
      = evm1.getCode a := rfl

/-- The CALL-family return path preserves code at every address, given the child
frame preserved it: `memWrite` touches memory only, and `incorporateChild*`
installs the child's state, whose code map the child preserved. -/
lemma Resume.call_getCode {parent : Devm} {a : Adr} {outputIndex outputSize : Nat}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : MsgResult.getCode r a = parent.getCode a) :
    Execution.getCode ((Resume.call parent outputIndex outputSize).run r) a =
      parent.getCode a := by
  have hmw : ∀ (d : Devm) (o : Bytes),
      (d.memWrite outputIndex o).getCode a = d.getCode a := fun d o =>
    (liftMachPure_worldEq (Mach.memWrite · outputIndex o) d).getCode a |>.symm
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;>
    dsimp only [bind, Except.bind]
  · dsimp only [MsgResult.getCode] at h
    dsimp only [Execution.getCode]
    change state.getCode a = parent.getCode a
    exact h
  · dsimp only [MsgResult.getCode] at h
    split
    · rcases hpush : (incorporateChildOnError parent child child.output).push 0 with
        e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
      · exact hp.trans h
      · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
        rw [hmw]
        exact hp.trans h
    · rcases hpush : (incorporateChildOnSuccess parent child child.output).push 1 with
        e | evm2 <;> have hp := Devm.push_getCode_gen hpush a
      · exact hp.trans h
      · show (evm2.memWrite outputIndex _).getCode a = parent.getCode a
        rw [hmw]
        exact hp.trans h

/-- On the successful path the CREATE-family return installs the child's
world; the status push leaves it alone. -/
lemma Resume.create_state {parent child : Devm} {newAddress : Adr} {sf : Devm}
    (h : (Resume.create parent newAddress).run (.ok child) = .ok sf) :
    sf.state = child.state := by
  have key : ∀ d : Devm, d.state = child.state → ∀ v : B256,
      Devm.push v d = .ok sf → sf.state = child.state := by
    intro d hd v hh
    have hframe := Devm.push_instructionFrame v d
    rw [hh] at hframe
    have hframe' : Devm.InstructionFrame d sf := hframe
    rw [← hframe'.state, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child []) rfl _ h

/-- A failed child message aborts the CALL-family return path. -/
lemma Resume.call_run_error {parent : Devm} {oi os : Nat}
    {e : EvmError × Jaune.State × AdrSet × Tra} {sf : Devm}
    (h : (Resume.call parent oi os).run (.error e) = .ok sf) : False := by
  rcases e with ⟨err, st, ac, tra⟩
  unfold Resume.run liftToExecution at h
  cases h

/-- On the successful path the CALL-family return installs the child's world;
the status push and the memory write leave it alone. -/
lemma Resume.call_state {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    sf.state = child.state := by
  have key : ∀ d : Devm, d.state = child.state → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      sf.state = child.state := by
    intro d hd v hh
    have hframe := Devm.push_instructionFrame v d
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh hframe
    · cases hh
    · injection hh with hh
      subst hh
      have hframe' : Devm.InstructionFrame d evm2 := hframe
      rw [← (Devm.memWrite_instructionFrame evm2 oi (child.output.take os)).state,
        ← hframe'.state, hd]
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

lemma GenericCall.codePreserve
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {exn : Execution}
    (inv : xl.InvGetCode)
    (run : GenericCall sevm devm gas value caller target codeAddress shouldTransferValue isStaticcall input_index input_size output_index output_size code disablePrecompiles xl exn) :
    Execution.CodePreserve devm exn := by
  intro a ha
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    rw [Devm.push_getCode_gen heq a]
    rfl
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    rw [Resume.call_getCode ?_]
    · rfl
    · rw [ProcessMessage.codePreserve inv hframe a
        (by rw [callMsg_benv_state_getCode]; exact ha)]
      exact callMsg_benv_state_getCode a

/-- A call-type step whose `Except` prefix failed carries that failure. -/
lemma XStep.run_ofExcept_error {e : EvmError × Devm} {xl : Xlot} {ex : Execution}
    (h : XStep.Run (XStep.ofExcept (.error e)) xl ex) : ex = .error e := h.2

/-! ### The dispatch shape of a call-type instruction

Everything `Xinst.step` does before dispatching — popping operands, charging
gas, extending memory, recording accesses, resolving delegations — stays inside
the instruction frame.  Recording that once, together with the two dispatch
targets and the provenance of the child's code, is what replaces the six
per-constructor bind walks the old mirrors forced: every `Xinst`-level master
below is a three-case argument over `Shape`. -/

def Xinst.Shape (sevm : Sevm) (devm : Devm) (s : XStep) : Prop :=
  (∃ ex, s = .done ex ∧ Execution.Rel Devm.InstructionFrame devm ex) ∨
  (∃ d endowment newAddress mi ms,
      Devm.InstructionFrame devm d ∧
      s = genericCreate.step sevm d endowment newAddress mi ms) ∨
  (∃ d d₀ gas value caller target codeAddress stv isSt ii isz oi osz code dp,
      Devm.InstructionFrame devm d ∧
      Devm.InstructionFrame devm d₀ ∧
      ( (stv = true ∧ caller = sevm.currentTarget) ∨
        (stv = false ∧ target = sevm.currentTarget) ) ∧
      ( target = sevm.currentTarget ∨
        ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target ) ) ∧
      s = genericCall.step sevm d gas value caller target codeAddress stv isSt
            ii isz oi osz code dp)

lemma Xinst.Shape.trans_left {sevm : Sevm} {a b : Devm} {s : XStep}
    (hab : Devm.InstructionFrame a b) (h : Xinst.Shape sevm b s) :
    Xinst.Shape sevm a s := by
  rcases h with ⟨ex, rfl, hex⟩ | ⟨d, e, na, mi, ms, hf, rfl⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, hf₀, hcal, hsrc, rfl⟩
  · exact Or.inl ⟨ex, rfl,
      Execution.Rel.trans_left Devm.instructionFrame_trans hab hex⟩
  · exact Or.inr (Or.inl ⟨d, e, na, mi, ms,
      Devm.instructionFrame_trans hab hf, rfl⟩)
  · exact Or.inr (Or.inr ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz,
      code, dp, Devm.instructionFrame_trans hab hf,
      Devm.instructionFrame_trans hab hf₀, hcal, hsrc, rfl⟩)

lemma Xinst.shape_done {sevm : Sevm} {devm : Devm} {ex : Execution}
    (h : Execution.Rel Devm.InstructionFrame devm ex) :
    Xinst.Shape sevm devm (.done ex) := Or.inl ⟨ex, rfl, h⟩

lemma Xinst.shape_error {sevm : Sevm} {devm : Devm} {err : EvmError × Devm}
    (h : Devm.InstructionFrame devm err.2) :
    Xinst.Shape sevm devm (XStep.ofExcept (.error err)) := Xinst.shape_done h

lemma Xinst.shape_create {sevm : Sevm} {devm d : Devm} {endowment : B256}
    {newAddress : Adr} {mi ms : Nat} (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (genericCreate.step sevm d endowment newAddress mi ms) :=
  Or.inr (Or.inl ⟨d, endowment, newAddress, mi, ms, hf, rfl⟩)

lemma Xinst.shape_call {sevm : Sevm} {devm d d₀ : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {ii isz oi osz : Nat}
    {code : ByteArray} {dp : Bool}
    (hf : Devm.InstructionFrame devm d) (hf₀ : Devm.InstructionFrame devm d₀)
    (hcal : (stv = true ∧ caller = sevm.currentTarget) ∨
      (stv = false ∧ target = sevm.currentTarget))
    (hsrc : target = sevm.currentTarget ∨
      ( ¬ isValidDelegation (d₀.getCode target) → code = d₀.getCode target )) :
    Xinst.Shape sevm devm
      (genericCall.step sevm d gas value caller target codeAddress stv isSt
        ii isz oi osz code dp) :=
  Or.inr (Or.inr ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isSt,
    ii, isz, oi, osz, code, dp, hf, hf₀, hcal, hsrc, rfl⟩)

lemma Xinst.shape_bind {sevm : Sevm} {devm d : Devm} {α : Type}
    {x : Except (EvmError × Devm) (α × Devm)}
    {f : α × Devm → Except (EvmError × Devm) XStep}
    (hd : Devm.InstructionFrame devm d)
    (hx : Outcome.Rel Prod.snd Prod.snd Devm.InstructionFrame d x)
    (hf : ∀ (v : α) (d' : Devm), Devm.InstructionFrame devm d' →
      Xinst.Shape sevm devm (XStep.ofExcept (f ⟨v, d'⟩))) :
    Xinst.Shape sevm devm (XStep.ofExcept (x >>= f)) := by
  rcases x with e | ⟨v, d'⟩
  · exact Xinst.shape_error (Devm.instructionFrame_trans hd hx)
  · exact hf v d' (Devm.instructionFrame_trans hd hx)

lemma Xinst.shape_bindE {sevm : Sevm} {devm d : Devm} {x : Execution}
    {f : Devm → Except (EvmError × Devm) XStep}
    (hd : Devm.InstructionFrame devm d)
    (hx : Execution.Rel Devm.InstructionFrame d x)
    (hf : ∀ d' : Devm, Devm.InstructionFrame devm d' →
      Xinst.Shape sevm devm (XStep.ofExcept (f d'))) :
    Xinst.Shape sevm devm (XStep.ofExcept (x >>= f)) := by
  rcases x with e | d'
  · exact Xinst.shape_error (Devm.instructionFrame_trans hd hx)
  · exact hf d' (Devm.instructionFrame_trans hd hx)

lemma Xinst.shape_assert {sevm : Sevm} {devm : Devm} {p : Prop} [Decidable p]
    {err : EvmError × Devm} {f : Unit → Except (EvmError × Devm) XStep}
    (herr : Devm.InstructionFrame devm err.2)
    (hf : Xinst.Shape sevm devm (XStep.ofExcept (f ()))) :
    Xinst.Shape sevm devm (XStep.ofExcept (Except.assert p err >>= f)) := by
  unfold Except.assert
  split
  · exact hf
  · exact Xinst.shape_error herr

/-- The early exit taken when the caller cannot cover the transferred value:
a push onto a machine whose world is untouched. -/
lemma Xinst.shape_shortfall {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withReturnData []).withGasLeft
            (d'.gasLeft + stipend)))))) := by
  refine Xinst.shape_bindE hf (Devm.push_instructionFrame 0 d) fun d' hf' => ?_
  exact Xinst.shape_done
    (Devm.instructionFrame_trans hf'
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl))

lemma Xinst.shape_shortfall' {sevm : Sevm} {devm d : Devm} {stipend : Nat}
    (hf : Devm.InstructionFrame devm d) :
    Xinst.Shape sevm devm
      (XStep.ofExcept
        (d.push 0 >>= fun d' =>
          .ok (XStep.done (.ok ((d'.withGasLeft
            (d'.gasLeft + stipend)).withReturnData []))))) := by
  refine Xinst.shape_bindE hf (Devm.push_instructionFrame 0 d) fun d' hf' => ?_
  exact Xinst.shape_done
    (Devm.instructionFrame_trans hf'
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl))

/-- Delegation resolution is the identity when the callee is not a delegating
EOA, so the child's code is exactly the callee's own code. -/
lemma accessDelegation_of_not_delegation {d : Devm} {adr : Adr}
    (h : ¬ isValidDelegation (d.getCode adr)) :
    accessDelegation d adr = ⟨false, adr, d.getCode adr, 0, d⟩ := by
  have hnone : getDelegatedCodeAddress (d.state.getCode adr) = none := by
    dsimp only [getDelegatedCodeAddress]
    rw [if_neg (show ¬ isValidDelegation (d.state.getCode adr) from h)]
  dsimp only [accessDelegation]
  rw [hnone]
  rfl

lemma Xinst.step_shape (sevm : Sevm) (devm : Devm) (x : Xinst) :
    Xinst.Shape sevm devm (Xinst.step sevm devm x) := by
  cases x with
  | create =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bindE h3 (chargeGas_instructionFrame _ d3) fun d4 h4 => ?_
    exact Xinst.shape_create
      (Devm.instructionFrame_trans h4 (Devm.memExtends_instructionFrame d4 _))
  | create2 =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToNat_instructionFrame d1) fun _ d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.pop_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bindE h4 (chargeGas_instructionFrame _ d4) fun d5 h5 => ?_
    exact Xinst.shape_create
      (Devm.instructionFrame_trans h5 (Devm.memExtends_instructionFrame d5 _))
  | call =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
      fun callee d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
    refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
    refine Xinst.shape_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
    have h7' : Devm.InstructionFrame devm (addAccessedAddress d7 callee) :=
      Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 callee)
    have hacc :=
      accessDelegation_instructionFrame (addAccessedAddress d7 callee) callee
    rcases hdel : accessDelegation (addAccessedAddress d7 callee) callee with
      ⟨dpv, na, cd, dagc, d8⟩
    rw [hdel] at hacc
    have h8 : Devm.InstructionFrame devm d8 :=
      Devm.instructionFrame_trans h7' hacc
    refine Xinst.shape_bindE h8 (chargeGas_instructionFrame _ d8) fun d9 h9 => ?_
    refine Xinst.shape_assert h9 ?_
    split
    · exact Xinst.shape_shortfall
        (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
    · refine Xinst.shape_call
        (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
        h7' (Or.inl ⟨rfl, rfl⟩) (Or.inr fun hnd => ?_)
      rw [accessDelegation_of_not_delegation hnd] at hdel
      exact (congrArg (fun t => t.2.2.1) hdel).symm
  | callcode =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
      fun cadr d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.pop_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
    refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
    refine Xinst.shape_bind h6 (Devm.popToNat_instructionFrame d6) fun _ d7 h7 => ?_
    have h7' : Devm.InstructionFrame devm (addAccessedAddress d7 cadr) :=
      Devm.instructionFrame_trans h7 (addAccessedAddress_instructionFrame d7 cadr)
    have hacc :=
      accessDelegation_instructionFrame (addAccessedAddress d7 cadr) cadr
    rcases hdel : accessDelegation (addAccessedAddress d7 cadr) cadr with
      ⟨dpv, na, cd, dagc, d8⟩
    rw [hdel] at hacc
    have h8 : Devm.InstructionFrame devm d8 :=
      Devm.instructionFrame_trans h7' hacc
    refine Xinst.shape_bindE h8 (chargeGas_instructionFrame _ d8) fun d9 h9 => ?_
    split
    · exact Xinst.shape_shortfall'
        (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
    · exact Xinst.shape_call
        (Devm.instructionFrame_trans h9 (Devm.memExtends_instructionFrame d9 _))
        h7' (Or.inl ⟨rfl, rfl⟩) (Or.inl rfl)
  | delcall =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
      fun cadr d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
    refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
    have h6' : Devm.InstructionFrame devm (addAccessedAddress d6 cadr) :=
      Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 cadr)
    have hacc :=
      accessDelegation_instructionFrame (addAccessedAddress d6 cadr) cadr
    rcases hdel : accessDelegation (addAccessedAddress d6 cadr) cadr with
      ⟨dpv, na, cd, dagc, d7⟩
    rw [hdel] at hacc
    have h7 : Devm.InstructionFrame devm d7 :=
      Devm.instructionFrame_trans h6' hacc
    refine Xinst.shape_bindE h7 (chargeGas_instructionFrame _ d7) fun d8 h8 => ?_
    exact Xinst.shape_call
      (Devm.instructionFrame_trans h8 (Devm.memExtends_instructionFrame d8 _))
      h6' (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
  | statcall =>
    simp only [Xinst.step]
    refine Xinst.shape_bind (Devm.instructionFrame_refl devm)
      (Devm.pop_instructionFrame devm) fun _ d1 h1 => ?_
    refine Xinst.shape_bind h1 (Devm.popToAdr_instructionFrame d1)
      fun tgt d2 h2 => ?_
    refine Xinst.shape_bind h2 (Devm.popToNat_instructionFrame d2) fun _ d3 h3 => ?_
    refine Xinst.shape_bind h3 (Devm.popToNat_instructionFrame d3) fun _ d4 h4 => ?_
    refine Xinst.shape_bind h4 (Devm.popToNat_instructionFrame d4) fun _ d5 h5 => ?_
    refine Xinst.shape_bind h5 (Devm.popToNat_instructionFrame d5) fun _ d6 h6 => ?_
    have h6' : Devm.InstructionFrame devm (addAccessedAddress d6 tgt) :=
      Devm.instructionFrame_trans h6 (addAccessedAddress_instructionFrame d6 tgt)
    have hacc :=
      accessDelegation_instructionFrame (addAccessedAddress d6 tgt) tgt
    rcases hdel : accessDelegation (addAccessedAddress d6 tgt) tgt with
      ⟨dpv, na, cd, dagc, d7⟩
    rw [hdel] at hacc
    have h7 : Devm.InstructionFrame devm d7 :=
      Devm.instructionFrame_trans h6' hacc
    refine Xinst.shape_bindE h7 (chargeGas_instructionFrame _ d7) fun d8 h8 => ?_
    refine Xinst.shape_call
      (Devm.instructionFrame_trans h8 (Devm.memExtends_instructionFrame d8 _))
      h6' (Or.inl ⟨rfl, rfl⟩) (Or.inr fun hnd => ?_)
    rw [accessDelegation_of_not_delegation hnd] at hdel
    exact (congrArg (fun t => t.2.2.1) hdel).symm

/-! ### What a spawned child frame starts from

`Prog.At` bookkeeping has to survive a suspension: the child's initial machine
must still see the contract's code, and — when the child *is* the contract —
must start at `pc = 0` with that code loaded.  With the interpreter flattened
all of this is read off the frame-entry equation plus one dispatch-level case
split, which is what the old six-lemma `prep_*` family did by hand. -/

lemma ByteArray.eq_empty_of_size_eq_zero {b : ByteArray} (h : b.size = 0) :
    b = .empty := by
  cases b with
  | mk data =>
    cases data with
    | mk l =>
      cases l with
      | nil => rfl
      | cons _ _ => contradiction

lemma Frame.enter_run_pc {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    cevm.pc = 0 := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_code {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    cevm.sta.code = f.inner.code := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_currentTarget {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) :
    cevm.sta.currentTarget = f.inner.currentTarget := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv h; rfl

lemma Frame.enter_run_getCode {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) (a : Adr) :
    cevm.dyna.getCode a = f.inner.benv.state.getCode a := by
  obtain ⟨benv, hbenv, rfl⟩ := Frame.enter_run_inv h
  exact benvAfterTransfer_ok_getCode hbenv a

lemma genericCreate.step_spawn_frame
    {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {f : Frame} {rsm : Resume}
    (hs : genericCreate.step sevm devm endowment newAddress mi ms
      = .spawn f rsm) :
    (∀ a : Adr, f.inner.benv.state.getCode a = devm.getCode a) ∧
      f.inner.currentTarget = newAddress ∧
      devm.getCode newAddress = .empty := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  rename_i h_collision
  have hpar : ∀ b : Adr,
      (addAccessedAddress
        (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress).getCode b
        = devm.getCode b := by
    intro b
    rw [addAccessedAddress_getCode]
    exact Devm.incrNonce_getCode
  refine ⟨fun a => ?_, rfl, ?_⟩
  · simp only [Frame.ofCreate]
    rw [processCreateMessage.msg_getCode, createMsg_benv_state_getCode]
    exact hpar a
  · push Not at h_collision
    rw [← hpar newAddress]
    exact ByteArray.eq_empty_of_size_eq_zero h_collision.2.1

lemma genericCall.step_spawn_frame
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool}
    {ii isz oi osz : Nat} {code : ByteArray} {dp : Bool}
    {f : Frame} {rsm : Resume}
    (hs : genericCall.step sevm devm gas value caller target codeAddress stv
      isSt ii isz oi osz code dp = .spawn f rsm) :
    (∀ a : Adr, f.inner.benv.state.getCode a = devm.getCode a) ∧
      f.inner.currentTarget = target ∧ f.inner.code = code := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  exact ⟨fun _ => rfl, rfl, rfl⟩

lemma Xinst.step_spawn_getCode {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (hs : Xinst.step sevm devm x = .spawn f rsm)
    (a : Adr) : f.inner.benv.state.getCode a = devm.getCode a := by
  rcases Xinst.step_shape sevm devm x with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · rw [(genericCreate.step_spawn_frame hs).1 a, hf.getCode a]
  · rw [(genericCall.step_spawn_frame hs).1 a, hf.getCode a]

/-- Where a spawned child's code comes from.  Create frames enter fresh code at
an address that had none; `CALLCODE`/`DELEGATECALL` keep the parent's target;
the remaining call kinds load the callee's own code unless it delegates. -/
lemma Xinst.step_spawn_source {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} (hs : Xinst.step sevm devm x = .spawn f rsm) :
    devm.getCode f.inner.currentTarget = .empty ∨
    f.inner.currentTarget = sevm.currentTarget ∨
    ( ¬ isValidDelegation (devm.getCode f.inner.currentTarget) →
        f.inner.code = devm.getCode f.inner.currentTarget ) := by
  rcases Xinst.step_shape sevm devm x with ⟨ex, hsh, -⟩ |
    ⟨d, e, na, mi, ms, hf, hsh⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, hf₀, -, hsrc, hsh⟩ <;> rw [hsh] at hs
  · cases hs
  · obtain ⟨-, htgt, hempty⟩ := genericCreate.step_spawn_frame hs
    exact Or.inl (by rw [htgt, hf.getCode na]; exact hempty)
  · obtain ⟨-, htgt, hcode⟩ := genericCall.step_spawn_frame hs
    rcases hsrc with rfl | hsrc
    · exact Or.inr (Or.inl htgt)
    · refine Or.inr (Or.inr fun hnd => ?_)
      rw [htgt] at hnd ⊢
      rw [hf₀.getCode t] at hnd ⊢
      rw [hcode]
      exact hsrc hnd

/-- Everything the child slot has to know about its own program location. -/
lemma Evm.step_spawn_child {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat} {cevm : Evm}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc')
    (he : f.enter = .run cevm) :
    cevm.pc = 0 ∧
    (∀ a : Adr, cevm.dyna.getCode a = devm.getCode a) ∧
    ( sevm.currentTarget ≠ cevm.sta.currentTarget →
      devm.getCode cevm.sta.currentTarget ≠ .empty →
      ¬ isValidDelegation (devm.getCode cevm.sta.currentTarget) →
      cevm.sta.code = devm.getCode cevm.sta.currentTarget ) := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hs
  have htgt := Frame.enter_run_currentTarget he
  have hcode := Frame.enter_run_code he
  refine ⟨Frame.enter_run_pc he, fun a => ?_, fun hne hnotEmpty hnotDel => ?_⟩
  · rw [Frame.enter_run_getCode he a]
    exact Xinst.step_spawn_getCode hx a
  · rw [htgt] at hne hnotEmpty hnotDel ⊢
    rw [hcode]
    rcases Xinst.step_spawn_source hx with hempty | hsame | hsrc
    · exact absurd hempty hnotEmpty
    · exact absurd hsame.symm hne
    · exact hsrc hnotDel

lemma chargeGas_getCode_err {cost devm err} (h : chargeGas cost devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (chargeGas_worldEq_of_error h).getCode a |>.symm

lemma Devm.push_getCode_err {v devm err} (h : Devm.push v devm = Except.error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMachExecution_worldEq_of_error (core := Mach.push v) h).getCode a |>.symm

lemma Devm.popToAdr_getCode_err {devm err} (h : Devm.popToAdr devm = .error err) (a : Adr) : err.2.getCode a = devm.getCode a := by
  exact (liftMach_worldEq_of_error (core := Mach.popToAdr) h).getCode a |>.symm

lemma Rinst.preserves_getCode_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getCode a = devm.getCode a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Devm.StateWriteFrame.getCode_eq hf a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact congrFun (congrArg (fun s => fun a => (s.get a).code) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (Devm.InstructionFrame.getCode hf a).symm

lemma Rinst.preserves_getCode_gen
    {pc sevm devm r exn}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = exn) (a : Adr)
    (_ne : (devm.getCode a).toList ≠ []) :
    Execution.getCode exn a = devm.getCode a := by
  cases exn <;> first | exact Rinst.preserves_getCode_err run a | exact Rinst.preserves_getCode run a

lemma Jinst.preserves_getCode
    {pc sevm devm j pc' devm'}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) (a : Adr) :
    devm'.getCode a = devm.getCode a := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (hf.getCode a).symm

def JumpResult.getCode (ex : Except (EvmError × Devm) (Nat × Devm)) (a : Adr) : ByteArray :=
  match ex with
  | .ok ⟨_, devm⟩ => devm.getCode a
  | .error ⟨_, devm⟩ => devm.getCode a

lemma Jinst.preserves_getCode_gen
    {pc sevm devm j ex}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j ex) :
    ∀ a : Adr, JumpResult.getCode ex a = devm.getCode a := by
  intro a
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  cases ex <;> exact (hf.getCode a).symm

lemma Linst.dest_preserves_getCode {sevm : Sevm} {devm : Devm} {exn : Execution}
    (run : Linst.Run sevm devm .dest exn) :
    ∀ adr : Adr, Execution.getCode exn adr = devm.getCode adr := by
  intro adr
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : devm.popToAdr <;> dsimp
  case error err =>
    intro run; rw [← run]; exact (Devm.popToAdr_getCode_err h1 adr)
  case ok res1 =>
    have h_acc : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getCode adr = res1.2.getCode adr := by
      split
      · exact addAccessedAddress_getCode
      · rfl
    cases h2 : chargeGas (if ((if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧ ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount else (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2) (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err =>
      intro run; rw [← run]
      change err.2.getCode adr = devm.getCode adr
      exact (chargeGas_getCode_err h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
    case ok res2 =>
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run; rw [← run]
        dsimp [assertDynamic, Except.assert] at h3
        split at h3
        · contradiction
        · simp only [Except.error.injEq] at h3; subst h3
          change res2.getCode adr = devm.getCode adr
          exact (chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run; rw [← run]
          change res2.getCode adr = devm.getCode adr
          exact (chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))
        case some res3 =>
          have h_sub : res3.getCode adr = res2.getCode adr := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none =>
              rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              change st.getCode adr = res2.getCode adr
              exact State.subBal_getCode h_st
          by_cases h_if : sevm.currentTarget ∈ (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos]
            intro run; rw [← run]
            change (addAccountToDelete _ _).getCode adr = devm.getCode adr
            have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr = res3.getCode adr := by
              dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
            have h_set : ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode adr = (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr := by
              dsimp [Devm.setBal, Devm.getCode]; exact State.setBal_getCode _ _ _ _
            have h_del : (addAccountToDelete ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0) sevm.currentTarget).getCode adr = ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode adr := by
              rfl
            exact h_del.trans (h_set.trans (h_add.trans (h_sub.trans ((chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))))))
          · simp only [h_if]
            intro run; rw [← run]
            change (res3.addBal _ _).getCode adr = devm.getCode adr
            have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode adr = res3.getCode adr := by
              dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
            exact h_add.trans (h_sub.trans ((chargeGas_getCode_eq h2 adr).trans (h_acc.trans (Devm.popToAdr_getCode_eq h1 adr))))

/-- Pointwise equality of code maps: the frame every non-create step keeps. -/
def Devm.CodeFrame (before after : Devm) : Prop :=
  ∀ a : Adr, after.getCode a = before.getCode a

theorem Linst.run_codeFrame {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution} (run : Linst.Run sevm devm l exn) :
    Execution.Rel Devm.CodeFrame devm exn := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · cases exn <;> exact Linst.dest_preserves_getCode run
  · have hf := Linst.run_instructionFrame sevm devm l h_not_dest
    rw [run] at hf
    cases exn <;> exact fun a => (hf.getCode a).symm

/-- Relational invariant carried by a filled recursive execution slot. -/
def Xlot.Rel (R : Devm → Devm → Prop) : Xlot → Prop
  | .none => True
  | .some ⟨evm, out⟩ => Execution.Rel R evm.dyna out

/-- Canonical outcome-aware effect of a regular instruction. -/
def Rinst.Effect (R : Devm → Devm → Prop) (r : Rinst) : Prop :=
  ∀ {pc sevm pre out},
    Rinst.run ⟨pc, sevm, pre⟩ r = out → Execution.Rel R pre out

/-- Canonical outcome-aware effect of a jump instruction. -/
def Jinst.Effect (R : Devm → Devm → Prop) (j : Jinst) : Prop :=
  ∀ {evm out},
    Jinst.Run evm j out →
      Outcome.Rel Prod.snd Prod.snd R evm.dyna out

/-- Canonical outcome-aware effect of a terminal instruction. -/
def Linst.Effect (R : Devm → Devm → Prop) (l : Linst) : Prop :=
  ∀ {sevm pre out},
    Linst.Run sevm pre l out → Execution.Rel R pre out

/-- Recursive-execution effect, parameterized by the relation on its child slot. -/
def Xinst.EffectRec (R : Devm → Devm → Prop) (x : Xinst) : Prop :=
  ∀ {sevm pre xl out},
    Xlot.Rel R xl → Xinst.Run sevm pre x xl out → Execution.Rel R pre out

/-- Nonterminal effect consumed by the mutual `Exec.effect` traversal. -/
def Ninst.EffectRec (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {pc sevm pre xl out},
    Xlot.Rel R xl → Ninst.StepRun pc sevm pre n xl out → Execution.Rel R pre out

/-- Successful-run relational projection used by `Func.effect`. -/
def Ninst.Effect (R : Devm → Devm → Prop) (n : Ninst) : Prop :=
  ∀ {sevm pre post}, Ninst.Run sevm pre n post → R pre post

lemma Ninst.effectRec_reg {R : Devm → Devm → Prop} {r : Rinst}
    (hr : Rinst.Effect R r) : Ninst.EffectRec R (.reg r) := by
  intro pc sevm pre xl out hxl hrun
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hrun
  obtain ⟨-, rfl⟩ := hrun
  exact hr rfl

lemma Ninst.effectRec_exec {R : Devm → Devm → Prop} {x : Xinst}
    (hx : Xinst.EffectRec R x) : Ninst.EffectRec R (.exec x) := by
  intro pc sevm pre xl out hxl hrun
  simp only [Ninst.StepRun, Ninst.step_exec] at hrun
  exact hx hxl (XStep.run_toStep.mp hrun)

/-- One step of the driver, related through whichever instruction the program
counter decodes to.  With the interpreter flattened this is the single place
where the four decode branches are enumerated; `Exec.effect` below then only
has to compose steps. -/
lemma Evm.step_effect {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {devm : Devm} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel R xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl out) :
    Execution.Rel R devm out := by
  rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
  · rw [Evm.step_invOp hgi] at hrun
    obtain ⟨-, rfl⟩ := hrun
    exact hrefl _
  · cases i with
    | next n =>
      rw [Evm.step_next (n := n) hgi] at hrun
      exact hn n hxl hrun
    | jump j =>
      rw [Evm.step_jump (j := j) hgi] at hrun
      obtain ⟨-, hcase⟩ := Step.run_ofJump hrun
      have hjr := hj j (evm := ⟨pc, sevm, devm⟩) (out := j.run ⟨pc, sevm, devm⟩) rfl
      rcases hcase with ⟨e, hje, rfl⟩ | ⟨pc', d, hje, rfl⟩ <;> rw [hje] at hjr <;>
        exact hjr
    | last l =>
      rw [Evm.step_last (l := l) hgi] at hrun
      obtain ⟨-, rfl⟩ := hrun
      exact hl l rfl

/-- The load-bearing traversal: per-instruction canonical effects compose into
`Execution.Rel` for a complete `Exec` derivation.  Where the old proof had one
case per mutual-block constructor, it now has one per driver outcome. -/
theorem Exec.effect {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : Execution.Rel R pre out := by
  have hcomp : ∀ {a b : Devm} {o : Execution},
      R a b → Execution.Rel R b o → Execution.Rel R a o := by
    intro a b o hab hbo
    cases o <;> exact htrans hab hbo
  induction run with
  | halt hstep =>
    exact Evm.step_effect hrefl hn hj hl (xl := .none) trivial
      (by rw [hstep]; exact ⟨rfl, rfl⟩)
  | cont hstep _ ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .none) (out := .ok _) trivial
      (by rw [hstep]; exact ⟨rfl, rfl⟩)
  | doneErr hstep henter hr =>
    exact Evm.step_effect hrefl hn hj hl (xl := .none) trivial
      (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
  | doneOk hstep henter hr _ ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .none) (out := .ok _) trivial
      (by rw [hstep]; exact ⟨_, RunFrame.of_done henter, hr.symm⟩)
  | runErr hstep henter _ hr ihc =>
    exact Evm.step_effect hrefl hn hj hl (xl := .some ⟨_, _⟩) ihc
      (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)
  | runOk hstep henter _ hr _ ihc ih =>
    refine hcomp (?_ : R _ _) ih
    exact Evm.step_effect hrefl hn hj hl (xl := .some ⟨_, _⟩) (out := .ok _) ihc
      (by rw [hstep]; exact ⟨_, RunFrame.of_run henter, hr.symm⟩)

lemma Xlot.rel_of_filled {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l)
    {xl : Xlot} (hfilled : xl.Filled) : Xlot.Rel R xl := by
  cases xl with
  | none => trivial
  | some slot =>
    rcases slot with ⟨evm, out⟩
    rcases hfilled with ⟨hrun⟩
    exact Exec.effect hrefl htrans hn hj hl hrun

lemma Ninst.effect_of_effectRec {R : Devm → Devm → Prop}
    (hrefl : ReflexiveRel R) (htrans : TransitiveRel R)
    (hn : ∀ n, Ninst.EffectRec R n)
    (hj : ∀ j, Jinst.Effect R j)
    (hl : ∀ l, Linst.Effect R l) :
    ∀ n, Ninst.Effect R n := by
  intro n sevm pre post hrun
  rcases hrun with ⟨xl, hfilled, pc, hrun'⟩
  have hrel := Xlot.rel_of_filled hrefl htrans hn hj hl hfilled
  exact hn n hrel hrun'

theorem Func.effect {R : Devm → Devm → Prop}
    (htrans : TransitiveRel R)
    (hpop : ∀ xs pre post, Devm.PopBurn xs pre post → R pre post)
    (hburn : ∀ pre post, Devm.Burn pre post → R pre post)
    (hn : ∀ n, Ninst.Effect R n)
    (hl : ∀ l, Linst.Effect R l)
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : R pre post := by
  induction run with
  | zero pop run' ih =>
    exact htrans (hpop _ _ _ pop) ih
  | succ neq pop burn run' ih =>
    exact htrans (hpop _ _ _ pop) (htrans (hburn _ _ burn) ih)
  | last run' =>
    exact hl _ run'
  | next runi run' ih =>
    exact htrans (hn _ runi) ih
  | call eq burn run' ih =>
    exact htrans (hburn _ _ burn) ih

-- Relational form of code preservation: nonempty code is never modified.
def Devm.CodePreserve (pre post : Devm) : Prop :=
  ∀ a : Adr, (pre.getCode a).toList ≠ [] → post.getCode a = pre.getCode a

lemma codePreserve_refl_trans :
    ReflexiveRel Devm.CodePreserve ∧ TransitiveRel Devm.CodePreserve := by
  constructor
  · intro d a _; rfl
  · intro a b c hab hbc adr ha
    have h1 := hab adr ha
    have h2 : (b.getCode adr).toList ≠ [] := by rw [h1]; exact ha
    exact (hbc adr h2).trans h1

lemma Xlot.invGetCode_of_rel {xl : Xlot}
    (h : Xlot.Rel Devm.CodePreserve xl) : xl.InvGetCode := by
  rcases xl with _ | ⟨evm, exn⟩
  · trivial
  · intro a ha
    cases exn with
    | error e => exact (h a ha).symm
    | ok d => exact (h a ha).symm

/-- Reverse bridge: the observation invariant `InvGetCode` implies the
relational `Xlot.Rel Devm.CodePreserve`.  Together with
`Xlot.invGetCode_of_rel` this makes the two forms interchangeable, so the
legacy `Xinst.preserves_getCode_gen` can project through the relational master. -/
lemma Xlot.rel_of_invGetCode {xl : Xlot}
    (h : xl.InvGetCode) : Xlot.Rel Devm.CodePreserve xl := by
  rcases xl with _ | ⟨evm, exn⟩
  · trivial
  · cases exn with
    | error e => exact fun a ha => (h a ha).symm
    | ok d => exact fun a ha => (h a ha).symm

lemma Rinst.codePreserve_effect (r : Rinst) :
    Rinst.Effect Devm.CodePreserve r := by
  intro pc sevm pre out hrun
  have h := Rinst.preserves_getCode_gen hrun
  cases out <;> exact fun a ha => h a ha

/-- Canonical relational code-preservation master for `Xinst`.  This carries the
full per-constructor case analysis, composing the world-silent primitive frames
(pops, gas, memory, access bookkeeping) with the Step 7.3 generic-operation
masters `GenericCall.codePreserve` / `GenericCreate.codePreserve`.  The legacy
observation theorem `Xinst.preserves_getCode_gen` is a projection of this master via
the `Xlot.InvGetCode` / `Xlot.Rel Devm.CodePreserve` bridge. -/
lemma Xinst.codePreserve_effectRec (x : Xinst) :
    Xinst.EffectRec Devm.CodePreserve x := by
  intro sevm devm xl exn hxl run
  have inv : xl.InvGetCode := Xlot.invGetCode_of_rel hxl
  have lift : ∀ {d : Devm}, Devm.InstructionFrame devm d →
      Execution.CodePreserve d exn →
      Execution.Rel Devm.CodePreserve devm exn := by
    intro d hf h
    have key : ∀ a : Adr, (devm.getCode a).toList ≠ [] →
        Execution.getCode exn a = devm.getCode a := by
      intro a ha
      rw [hf.getCode a] at ha ⊢
      exact h a ha
    cases exn with
    | error e => exact fun a ha => key a ha
    | ok d' => exact fun a ha => key a ha
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm devm x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;>
    rw [hs] at run
  -- the whole step stayed inside the instruction frame
  · obtain ⟨-, rfl⟩ := run
    exact Outcome.Rel.mono (fun _ _ hfr a _ => (hfr.getCode a).symm) hframe
  -- dispatched to the CREATE family
  · exact lift hf (GenericCreate.codePreserve inv run)
  -- dispatched to the CALL family
  · exact lift hf (GenericCall.codePreserve inv run)

/-- Compatibility projection: the legacy observation theorem, now derived from
the relational master `Xinst.codePreserve_effectRec` through the
`Xlot.rel_of_invGetCode` bridge.  Statement unchanged. -/
lemma Xinst.preserves_getCode_gen
    {sevm devm x xl exn}
    (inv : xl.InvGetCode)
    (run : Xinst.Run sevm devm x xl exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      Execution.getCode exn a = devm.getCode a := by
  have h := Xinst.codePreserve_effectRec x (Xlot.rel_of_invGetCode inv) run
  cases exn with
  | error e => exact fun a ha => h a ha
  | ok d => exact fun a ha => h a ha

lemma Ninst.push_instructionFrame_effectRec
    {xs : Bytes} {hxs : xs.length ≤ 32} :
    Ninst.EffectRec Devm.InstructionFrame (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hRun
  obtain ⟨-, rfl⟩ := hRun
  apply Execution.Rel.bind Devm.instructionFrame_trans
    (chargeGas_instructionFrame (if xs = [] then gBase else gVerylow) pre)
  exact Devm.push_instructionFrame xs.toB256

lemma Ninst.push_effectRec_of_instructionFrame
    {R : Devm → Devm → Prop} {xs : Bytes} {hxs : xs.length ≤ 32}
    (hIR : ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → R d d') :
    Ninst.EffectRec R (.push xs hxs) := by
  intro pc sevm pre xl out hxl hRun
  have h0 : xl = .none := by
    simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hRun
    exact hRun.1
  subst h0
  exact Outcome.Rel.mono hIR
    (Ninst.push_instructionFrame_effectRec (hxs := hxs) (xl := .none)
      trivial hRun)

lemma Ninst.push_codePreserve_effectRec {xs : Bytes} {hxs : xs.length ≤ 32} :
  Ninst.EffectRec Devm.CodePreserve (.push xs hxs) := by
  exact Ninst.push_effectRec_of_instructionFrame (R := Devm.CodePreserve)
    (fun _ _ hf a _ => (hf.getCode a).symm)

lemma Ninst.codePreserve_effectRec (n : Ninst) :
    Ninst.EffectRec Devm.CodePreserve n := by
  cases n with
  | reg r =>
    exact Ninst.effectRec_reg (Rinst.codePreserve_effect r)
  | exec x =>
    exact Ninst.effectRec_exec (Xinst.codePreserve_effectRec x)
  | push xs hxs =>
    exact Ninst.push_codePreserve_effectRec

lemma Jinst.codePreserve_effect (j : Jinst) :
    Jinst.Effect Devm.CodePreserve j := by
  intro evm out hrun
  have hf := Jinst.run_instructionFrame evm j
  rw [hrun] at hf
  cases out <;> exact fun a _ => (hf.getCode a).symm

lemma Linst.codePreserve_effect (l : Linst) :
    Linst.Effect Devm.CodePreserve l := by
  intro sevm pre out hrun
  have hf := Linst.run_codeFrame hrun
  cases out <;> exact fun a _ => hf a

lemma Exec.preserves_getCode {pc} {sevm} {devm} {exn}
    (run : Exec pc sevm devm exn) :
    ∀ a : Adr,
      (devm.getCode a).toList ≠ [] →
      Execution.getCode exn a = devm.getCode a := by
  intro a ha
  have h := Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect
    Linst.codePreserve_effect run
  cases exn with
  | error e => exact h a ha
  | ok d => exact h a ha

lemma not_empty_of_compile {p : Prog} {code : ByteArray} (h : some code.toList = Prog.compile p) : code ≠ .empty := by
  intro hc
  have h_ne : Prog.compile p ≠ some [] := Prog.compile_ne_nil
  rw [←h, hc] at h_ne
  have h_empty_toList : ByteArray.empty.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    rfl
  rw [h_empty_toList] at h_ne
  exact h_ne rfl

lemma not_delegation_of_compile {p : Prog} {code : ByteArray}
    (h : some code.toList = Prog.compile p) : ¬ isValidDelegation code := by
  unfold isValidDelegation
  unfold Prog.compile at h
  unfold table at h
  simp only [Table.compile] at h
  simp only [bind] at h
  symm at h
  rcases of_bind_eq_some h with ⟨bs, h_bs, h'⟩
  rcases of_bind_eq_some h' with ⟨bss, h_bss, h_eq⟩
  injection h_eq with h_eq
  intro h_del
  rcases h_del with ⟨h_size, h_slice⟩
  have h_slice_eq : code.sliceD 0 3 0 = code.toList.sliceD 0 3 0 := ByteArray.sliceD_eq _ _ _ _
  rw [h_slice_eq, ←h_eq, eoaDelegationMarker] at h_slice
  revert h_slice
  simp only [List.sliceD]
  intro h_false
  injection h_false with h_false
  change (91 : UInt8) = 239 at h_false
  contradiction

/-- The "we are inside the contract" case, shared by every driver outcome:
either the run failed (nothing to prove) or it completed a program run at
`pc = 0`, which the depth induction turns into the contract-level invariant. -/
private lemma lift_core.atTarget
    {ε : Nat → Sevm → Devm → Execution → Prop} {π : Sevm → Devm → Devm → Prop}
    {ca : Adr} {p : Prog}
    (analog : ∀ {sevm pre post}, π sevm pre post → ε 0 sevm pre (.ok post))
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallDeeperAt sevm.depth ca p (fun pc s d e _ => ε pc s d e) →
        π sevm pre post )
    ( errAtTarget :
      ∀ {pc sevm devm err devm'},
        sevm.currentTarget = ca → ε pc sevm devm (.error ⟨err, devm'⟩) )
    {pc : Nat} {sevm : Sevm} {devm : Devm} {exn : Execution}
    (ex : Exec pc sevm devm exn)
    (h_fa : ForallDeeperAt sevm.depth ca p (fun pc s d e _ => ε pc s d e))
    (h_at_p : p.At ca pc sevm devm) (h_eq : sevm.currentTarget = ca) :
    ε pc sevm devm exn := by
  cases exn with
  | error e => exact errAtTarget h_eq
  | ok post =>
    have h_pc : pc = 0 := (h_at_p.right h_eq).right
    subst h_pc
    exact analog
      (depth_ind (correct sevm devm p post ex (h_at_p.right h_eq).left) h_eq h_fa)

/-- Code preservation across one driver step, in the form the `Prog.At`
bookkeeping needs. -/
private lemma lift_core.stepCode {pc : Nat} {sevm : Sevm} {devm devm' : Devm}
    {xl : Xlot} (hxl : Xlot.Rel Devm.CodePreserve xl)
    (hrun : Step.Run (Evm.step ⟨pc, sevm, devm⟩) xl (.ok devm'))
    (a : Adr) (ha : (devm.getCode a).toList ≠ []) :
    devm'.getCode a = devm.getCode a :=
  Evm.step_effect codePreserve_refl_trans.1 Ninst.codePreserve_effectRec
    Jinst.codePreserve_effect Linst.codePreserve_effect hxl hrun a ha

/-- The eliminator every contract-level invariant proof runs on: strong
induction on frame depth combined with the driver's case analysis, carrying the
program-location bookkeeping (`Prog.At`) across steps and across suspensions.
Its handlers stay indexed by *instruction kind*, so the decode dispatch happens
here once and `lift`/`lift_inv` are insulated from the flattening. -/
lemma lift_core
    (ε : Nat → Sevm → Devm → Execution → Prop)
    (π : Sevm → Devm → Devm → Prop)
    (analog : ∀ {sevm pre post}, π sevm pre post → ε 0 sevm pre (.ok post))
    (ca : Adr) (p : Prog)
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallDeeperAt sevm.depth ca p (fun pc s d e _ => ε pc s d e) →
        π sevm pre post )
    ( errAtTarget :
      ∀ {pc sevm devm err devm'},
        sevm.currentTarget = ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( invOp :
      ∀ {pc sevm devm},
        sevm.code.getInst pc = none →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨.halt (.invalidOpcode .none), devm⟩) )
    ( nextNoneErr :
      ∀ {pc sevm devm n err devm'},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n .none (.error ⟨err, devm'⟩) →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( nextSomeErr :
      ∀ {pc sevm devm n evm_ exn_ err devm'},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n (.some ⟨evm_, exn_⟩) (.error ⟨err, devm'⟩) →
        Exec evm_.pc evm_.sta evm_.dyna exn_ →
        sevm.currentTarget ≠ ca →
        ε evm_.pc evm_.sta evm_.dyna exn_ →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( nextNoneRec :
      ∀ {pc sevm devm n devm' exn},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n .none (.ok devm') →
        Exec (pc + n.size) sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε (pc + n.size) sevm devm' exn →
        ε pc sevm devm exn )
    ( nextSomeRec :
      ∀ {pc sevm devm n evm_ exn_ devm' exn},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm devm n (.some ⟨evm_, exn_⟩) (.ok devm') →
        Exec evm_.pc evm_.sta evm_.dyna exn_ →
        Exec (pc + n.size) sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε evm_.pc evm_.sta evm_.dyna exn_ →
        ε (pc + n.size) sevm devm' exn →
        ε pc sevm devm exn )
    ( jumpErr :
      ∀ {pc sevm devm j err devm'},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩) →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm (.error ⟨err, devm'⟩) )
    ( jumpRec :
      ∀ {pc sevm devm j pc' devm' exn},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩) →
        Exec pc' sevm devm' exn →
        sevm.currentTarget ≠ ca →
        ε pc' sevm devm' exn →
        ε pc sevm devm exn )
    ( last :
      ∀ {pc sevm devm l exn},
        Linst.At sevm.code pc l →
        Linst.Run sevm devm l exn →
        sevm.currentTarget ≠ ca →
        ε pc sevm devm exn ) :
    Exec.Fa (Exec.Wkn ca p (fun pc s d e _ => ε pc s d e)) := by
  apply Exec.strong_rec
  apply @Exec.rec (Fortify (Exec.Wkn ca p (fun pc s d e _ => ε pc s d e)))
  -- halt
  · intro pc sevm devm ex hstep h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.halt hstep) h_fa h_at_p h_eq
    · rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
      · rw [Evm.step_invOp hgi] at hstep
        cases hstep
        exact invOp hgi h_ne
      · cases i with
        | next n =>
          have hns : Ninst.step ⟨pc, sevm, devm⟩ n = .halt ex := by
            rw [← Evm.step_next (n := n) hgi]; exact hstep
          have hrun : Ninst.StepRun pc sevm devm n .none ex := by
            unfold Ninst.StepRun; rw [hns]; exact ⟨rfl, rfl⟩
          cases ex with
          | error e => exact nextNoneErr hgi hrun h_ne
          | ok d => exact absurd hns Ninst.step_ne_halt_ok
        | jump j =>
          rw [Evm.step_jump (j := j) hgi] at hstep
          rcases hj : j.run ⟨pc, sevm, devm⟩ with e | ⟨pc', devm'⟩ <;>
            rw [hj] at hstep <;> simp only [Step.ofJump] at hstep
          · cases hstep; exact jumpErr hgi hj h_ne
          · cases hstep
        | last l =>
          rw [Evm.step_last (l := l) hgi] at hstep
          cases hstep
          exact last hgi rfl h_ne
  -- cont
  · intro pc sevm devm pc' devm' exn hstep ex ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.cont hstep ex) h_fa h_at_p h_eq
    · have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core.stepCode (xl := .none) trivial
          (by rw [hstep]; exact ⟨rfl, rfl⟩) ca h_ne_code
      have h_at' : p.At ca pc' sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      rcases hgi : (Evm.getInst ⟨pc, sevm, devm⟩) with _ | i
      · rw [Evm.step_invOp hgi] at hstep; cases hstep
      · cases i with
        | next n =>
          have hns : Ninst.step ⟨pc, sevm, devm⟩ n = .cont pc' devm' := by
            rw [← Evm.step_next (n := n) hgi]; exact hstep
          have hpc : pc' = pc + n.size := Ninst.step_cont_pc hns
          subst hpc
          have hrun : Ninst.StepRun pc sevm devm n .none (.ok devm') := by
            unfold Ninst.StepRun; rw [hns]; exact ⟨rfl, rfl⟩
          exact nextNoneRec hgi hrun ex h_ne (ih h_fa h_at')
        | jump j =>
          rw [Evm.step_jump (j := j) hgi] at hstep
          exact jumpRec hgi (Step.ofJump_cont hstep) ex h_ne (ih h_fa h_at')
        | last l =>
          rw [Evm.step_last (l := l) hgi] at hstep; cases hstep
  -- doneErr
  · intro pc sevm devm f rsm pc' r e hstep henter hr h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.doneErr hstep henter hr) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, -⟩ := Evm.step_spawn_inv hstep
      have hrun : Ninst.StepRun pc sevm devm (.exec x) .none (.error e) := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨r, RunFrame.of_done henter, hr.symm⟩
      exact nextNoneErr hxat hrun h_ne
  -- doneOk
  · intro pc sevm devm f rsm pc' r devm' exn hstep henter hr ex ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.doneOk hstep henter hr ex) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, hpc'⟩ := Evm.step_spawn_inv hstep
      subst hpc'
      have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
      have hrun : Ninst.StepRun pc sevm devm (.exec x) .none (.ok devm') := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨r, RunFrame.of_done henter, hr.symm⟩
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core.stepCode (xl := .none) trivial
          (by rw [hstep]; exact ⟨r, RunFrame.of_done henter, hr.symm⟩) ca h_ne_code
      have h_at' : p.At ca (pc + 1) sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      exact nextNoneRec hxat hrun ex h_ne (ih h_fa h_at')
  -- runErr
  · intro pc sevm devm f rsm pc' cevm raw e hstep henter child hr ihc h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.runErr hstep henter child hr) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, -⟩ := Evm.step_spawn_inv hstep
      obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
      have hdepth : cevm.sta.depth < sevm.depth := by
        rw [Frame.enter_run_depth henter]; exact Step.spawn_depth_lt hstep
      have h_at_child : p.At ca cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [hgc ca]; exact h_at_p.left, fun hct => ⟨?_, hpc0⟩⟩
        have hne' : sevm.currentTarget ≠ cevm.sta.currentTarget := by
          rw [hct]; exact h_ne
        have hcode := hsrc hne'
          (by rw [hct]; exact not_empty_of_compile h_at_p.left)
          (by rw [hct]; exact not_delegation_of_compile h_at_p.left)
        rw [hcode, hct]
        exact h_at_p.left
      have hrun :
          Ninst.StepRun pc sevm devm (.exec x) (.some ⟨cevm, raw⟩) (.error e) := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩
      exact nextSomeErr hxat hrun child h_ne
        (h_fa cevm.pc cevm.sta cevm.dyna raw child hdepth h_at_child)
  -- runOk
  · intro pc sevm devm f rsm pc' cevm raw devm' exn hstep henter child hr ex
      ihc ih h_fa h_at_p
    rcases em (sevm.currentTarget = ca) with h_eq | h_ne
    · exact lift_core.atTarget analog depth_ind errAtTarget
        (.runOk hstep henter child hr ex) h_fa h_at_p h_eq
    · obtain ⟨x, hxat, -, hpc'⟩ := Evm.step_spawn_inv hstep
      subst hpc'
      obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hstep henter
      have hdepth : cevm.sta.depth < sevm.depth := by
        rw [Frame.enter_run_depth henter]; exact Step.spawn_depth_lt hstep
      have h_ne_code : (devm.getCode ca).toList ≠ [] := fun hc =>
        Prog.compile_ne_nil (Eq.trans h_at_p.left.symm (congrArg some hc))
      have h_at_child : p.At ca cevm.pc cevm.sta cevm.dyna := by
        refine ⟨by rw [hgc ca]; exact h_at_p.left, fun hct => ⟨?_, hpc0⟩⟩
        have hne' : sevm.currentTarget ≠ cevm.sta.currentTarget := by
          rw [hct]; exact h_ne
        have hcode := hsrc hne'
          (by rw [hct]; exact not_empty_of_compile h_at_p.left)
          (by rw [hct]; exact not_delegation_of_compile h_at_p.left)
        rw [hcode, hct]
        exact h_at_p.left
      have hchild : Xlot.Rel Devm.CodePreserve (.some ⟨cevm, raw⟩) :=
        Exec.effect codePreserve_refl_trans.1 codePreserve_refl_trans.2
          Ninst.codePreserve_effectRec Jinst.codePreserve_effect
          Linst.codePreserve_effect child
      have hrun :
          Ninst.StepRun pc sevm devm (.exec x) (.some ⟨cevm, raw⟩) (.ok devm') := by
        unfold Ninst.StepRun
        rw [← Evm.step_next (n := Ninst.exec x) hxat, hstep]
        exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩
      have hcode : devm'.getCode ca = devm.getCode ca :=
        lift_core.stepCode (xl := .some ⟨cevm, raw⟩) hchild
          (by rw [hstep]; exact ⟨f.settle raw, RunFrame.of_run henter, hr.symm⟩)
          ca h_ne_code
      have h_at' : p.At ca (pc + 1) sevm devm' :=
        ⟨by rw [hcode]; exact h_at_p.left, fun hc => (h_ne hc).elim⟩
      exact nextSomeRec hxat hrun child ex h_ne
        (h_fa cevm.pc cevm.sta cevm.dyna raw child hdepth h_at_child)
        (ih h_fa h_at')

lemma lift
    (R : Sevm → Devm → Devm → Prop)
    (ca : Adr) -- contract address
    (p : Prog)
    ( depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ForallSubExec sevm.depth ca p R →
        R sevm pre post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'}
        {exn' : Execution} {inter} {post},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n
          (.some ⟨evm', exn'⟩)
          (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna exn' →
        Exec (pc + n.size) sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        ifOk (R evm'.sta evm'.dyna) exn' →
        R sevm inter post →
        R sevm pre post )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter} {post},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        Exec pc' sevm inter (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm inter post →
        R sevm pre post )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        R sevm pre post ) :
    ∀ pc sevm pre post,
      Exec pc sevm pre (.ok post) →
      Prog.At p ca pc sevm pre →
      R sevm pre post := by
  intro pc sevm pre post h_exc h_at
  refine lift_core (fun _ sevm pre exn => ifOk (R sevm pre) exn) R (fun h => h) ca p
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ pc sevm pre (.ok post) h_exc h_at
  · intro sevm' pre' post' h_run h_eq h_fa
    apply depth_ind h_run h_eq
    intro pc_ sevm_ devm_ post_ h_exc' h_lt h_at'
    exact h_fa pc_ sevm_ devm_ (.ok post_) h_exc' h_lt h_at'
  · intro pc' sevm' devm' err devm'' h_eq; exact trivial
  · intro pc' sevm' devm' h_get h_ne; exact trivial
  · intro pc' sevm' devm' n err devm'' h_at' h_run h_ne; exact trivial
  · intro pc' sevm' devm' n evm_ exn_ err devm'' h_at' h_run ex_sub h_ne h_ih; exact trivial
  · intro pc' sevm' devm' n devm'' exn h_at' h_run ex h_ne h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact nextNone h_at' h_run ex h_ne h_ih
  · intro pc' sevm' devm' n evm_ exn_ devm'' exn h_at' h_run ex_sub ex h_ne h_ih_sub h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact nextSome h_at' h_run ex_sub ex h_ne h_ih_sub h_ih
  · intro pc' sevm' devm' j err devm'' h_at' h_run h_ne; exact trivial
  · intro pc' sevm' devm' j pc_ devm'' exn h_at' h_run ex h_ne h_ih
    cases exn with
    | error e => exact trivial
    | ok post' => exact jump h_at' h_run ex h_ne h_ih
  · intro pc' sevm' devm' l exn h_at' h_run h_ne
    cases exn with
    | error e => exact trivial
    | ok post' => exact last h_at' h_run h_ne

lemma lift_inv
    (ca : Adr) (p : Prog)
    (σ : Sevm → Devm → Prop)
    (ρ : Sevm → Devm → Prop)
    ( with_depth_ind :
      ∀ {sevm pre post},
        Prog.Run sevm pre p post →
        sevm.currentTarget = ca →
        ( ∀ pc' sevm' pre' post',
            Exec pc' sevm' pre' (.ok post') →
            sevm'.depth < sevm.depth →
            Prog.At p ca pc' sevm' pre' →
            σ sevm' pre' →
            ρ sevm' post' ) →
        σ sevm pre →
        ρ sevm post )
    ( nextNone :
      ∀ {pc} {sevm} {pre} {n} {inter},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n .none (.ok inter) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter )
    ( nextSome :
      ∀ {pc} {sevm} {pre} {n} {evm'} {exn'} {inter},
        Ninst.At sevm.code pc n →
        Ninst.StepRun pc sevm pre n (.some ⟨evm', exn'⟩) (.ok inter) →
        Exec evm'.pc evm'.sta evm'.dyna exn' →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ evm'.sta evm'.dyna ∧ (ifOk (ρ evm'.sta) exn' → σ sevm inter) )
    ( jump :
      ∀ {pc} {sevm} {pre} {j} {pc'} {inter},
        Jinst.At sevm.code pc j →
        Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        σ sevm inter )
    ( last :
      ∀ {pc} {sevm} {pre} {l} {post},
        Linst.At sevm.code pc l →
        Linst.Run sevm pre l (.ok post) →
        sevm.currentTarget ≠ ca →
        σ sevm pre →
        ρ sevm post ) :
    ∀ pc sevm devm post,
      Exec pc sevm devm (.ok post) →
      Prog.At p ca pc sevm devm →
      σ sevm devm →
      ρ sevm post := by
  apply @Blanc.lift (fun sevm pre post => σ sevm pre → ρ sevm post) ca p with_depth_ind
  · intro pc sevm pre n inter post h_at h_run _ h_ne h_ih h_pi
    exact h_ih (nextNone h_at h_run h_ne h_pi)
  · intro pc sevm pre n evm' exn' inter post h_at h_run ex_sub _ h_ne h_ifOk h_ih h_pi
    rcases nextSome h_at h_run ex_sub h_ne h_pi with ⟨h_pi_sub, h_imp⟩
    apply h_ih; apply h_imp
    cases exn' with
    | error e => exact trivial
    | ok post' => exact h_ifOk h_pi_sub
  · intro pc sevm pre j pc' inter post h_at h_run _ h_ne h_ih h_pi
    exact h_ih (jump h_at h_run h_ne h_pi)
  · intro pc sevm pre l post h_at h_run h_ne h_pi
    exact last h_at h_run h_ne h_pi

syntax "show_prefix_zero" : tactic
macro_rules
  | `(tactic| show_prefix_zero) =>
    `(tactic| intros h0 h1; apply append_pref h0.stack h1)

syntax "show_prefix_one" : tactic
macro_rules
  | `(tactic| show_prefix_one) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', h0⟩;
              rcases h0.stack with ⟨stk, h2, h3⟩; clear h0;
              rcases List.of_cons_pref_of_cons_pref h1 (pref_of_split h2) with ⟨hx, h⟩;
              cases hx; clear h; apply append_pref h3 (of_append_pref h2 h1) )

syntax "show_prefix_two" : tactic
macro_rules
  | `(tactic| show_prefix_two) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', y', h0⟩;
              rcases h0.stack with ⟨stk, h2, h3⟩; clear h0;
              rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩;
              cases hx; cases hy; clear h; apply append_pref h3 (of_append_pref h2 h1) )


infix:70 " <? "  => B256.ltCheck
infix:70 " >? "  => B256.gtCheck
infix:70 " ±<? " => B256.sltCheck
infix:70 " ±>? " => B256.sgtCheck
infix:70 " =? "  => B256.eqCheck

lemma Bytes.sig_zero_cons (xs) : Bytes.sig (0 :: xs) = Bytes.sig xs := rfl
lemma Bytes.sig_nonzero_cons (x xs) (h : x ≠ 0) : Bytes.sig (x :: xs) = x :: xs := by
  simp only [Jaune.Bytes.sig]; rw [List.dropWhile_cons_of_neg]; simp [h]

lemma Bytes.toB256_sig (bs : Bytes) : Bytes.toB256 (Bytes.sig bs) = bs.toB256 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : b = 0
    · cases h; rw [sig_zero_cons, ih, Bytes.toB256_zero_cons]
    · rw [sig_nonzero_cons b bs h]

def Stack.Diff (xs zs : Stack) (s s'' : Stack) : Prop :=
  ∃ s' : Stack, Stack.Pop xs s s' ∧ Stack.Push zs s' s''

def Stack.SwapCore (x y : B256) : Nat → Stack → Stack → Prop
  | 0, y' :: xs, x' :: xs' => x = x' ∧ y = y' ∧ xs = xs'
  | n + 1, z :: xs, z' :: xs' => z = z' ∧ SwapCore x y n xs xs'
  | _, _, _ => False

def Stack.Swap (n : Nat) : Stack → Stack → Prop
  | x :: xs, y :: xs' => SwapCore x y n xs xs'
  | _, _ => False

def Devm.Push (xs : List B256) : Devm → Devm → Prop :=
  Rel {Rels.eq with stack := Stack.Push xs}

def Devm.DiffBurn (xs ys : List B256) : Devm → Devm → Prop :=
  Rel {Rels.eq with stack := Stack.Diff xs ys, gasLeft := (· ≥ ·)}

lemma Devm.push_of_push {x : B256} {s s' : Devm} (h : Devm.push x s = .ok s') :
    Devm.Push [x] s s' := by
  rw [Devm.push_def] at h
  simp only [Except.assert, bind, Except.bind] at h
  split at h
  · cases h
  · injection h with eq; subst eq
    constructor <;>
      simp [Devm.Rels.eq, Stack.Push, Split, Devm.setMach]
    all_goals rfl

lemma Devm.pushBurn_of_burn_of_push {xs : List B256} {s s' s'' : Devm}
    (burn : Devm.Burn s s') (push : Devm.Push xs s' s'') :
    Devm.PushBurn xs s s'' := by
  constructor
  · exact burn.stack ▸ push.stack
  · exact Eq.trans burn.memory push.memory
  · rw [← push.gasLeft]; exact burn.gasLeft
  · exact Eq.trans burn.logs push.logs
  · exact Eq.trans burn.refundCounter push.refundCounter
  · exact Eq.trans burn.output push.output
  · exact Eq.trans burn.accountsToDelete push.accountsToDelete
  · exact Eq.trans burn.returnData push.returnData
  · exact Eq.trans burn.error push.error
  · exact Eq.trans burn.accessedAddresses push.accessedAddresses
  · exact Eq.trans burn.accessedStorageKeys push.accessedStorageKeys
  · exact Eq.trans burn.state push.state
  · exact Eq.trans burn.createdAccounts push.createdAccounts
  · exact Eq.trans burn.transientStorage push.transientStorage

lemma Devm.diffBurn_of_pop_of_pushBurn {xs ys : List B256} {s s' s'' : Devm}
    (pop : Devm.Pop xs s s') (push : Devm.PushBurn ys s' s'') :
    Devm.DiffBurn xs ys s s'' := by
  constructor
  · exact ⟨s'.stack, pop.stack, push.stack⟩
  · exact Eq.trans pop.memory push.memory
  · rw [pop.gasLeft]; exact push.gasLeft
  · exact Eq.trans pop.logs push.logs
  · exact Eq.trans pop.refundCounter push.refundCounter
  · exact Eq.trans pop.output push.output
  · exact Eq.trans pop.accountsToDelete push.accountsToDelete
  · exact Eq.trans pop.returnData push.returnData
  · exact Eq.trans pop.error push.error
  · exact Eq.trans pop.accessedAddresses push.accessedAddresses
  · exact Eq.trans pop.accessedStorageKeys push.accessedStorageKeys
  · exact Eq.trans pop.state push.state
  · exact Eq.trans pop.createdAccounts push.createdAccounts
  · exact Eq.trans pop.transientStorage push.transientStorage

lemma Devm.pushBurn_of_pushItem {v : B256} {cost : Nat} {s s' : Devm}
    (h : pushItem v cost s = .ok s') : Devm.PushBurn [v] s s' := by
  rw [pushItem_def] at h; exact Devm.pushBurn_of_run h

lemma Devm.diffBurn_of_applyUnary {f : B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyUnary f cost s = .ok s') :
    ∃ x, Devm.DiffBurn [x] [f x] s s' := by
  rw [applyUnary_def] at h
  rcases of_bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h2⟩
  simp only at h2
  rw [pushItem_def] at h2
  refine ⟨x, Devm.diffBurn_of_pop_of_pushBurn (Devm.pop_of_pop h1) (Devm.pushBurn_of_run h2)⟩

lemma Devm.diffBurn_of_applyBinary {f : B256 → B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyBinary f cost s = .ok s') :
    ∃ x y, Devm.DiffBurn [x, y] [f x y] s s' := by
  rw [applyBinary_def] at h
  rcases of_bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h'⟩
  rcases of_bind_eq_ok h' with ⟨⟨y, s₂⟩, h2, h3⟩
  simp only at h3
  rw [pushItem_def] at h3
  refine ⟨x, y, Devm.diffBurn_of_pop_of_pushBurn
    (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2))
    (Devm.pushBurn_of_run h3)⟩

lemma Devm.pop_of_popToNat {k : Nat} {devm devm' : Devm}
    (h : Devm.popToNat devm = .ok ⟨k, devm'⟩) :
    ∃ x, Devm.Pop [x] devm devm' := by
  rw [Devm.popToNat_def] at h
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩ <;> simp [hp] at h
  rcases h with ⟨_, rfl⟩
  exact ⟨x, Devm.pop_of_pop hp⟩

lemma of_run_reg {e : Sevm} {s s' : Devm} {r : Rinst}
    (h : Ninst.Run e s (Ninst.reg r) s') :
    ∃ pc, Rinst.run ⟨pc, e, s⟩ r = .ok s' := by
  rcases h with ⟨xl, _, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
  exact ⟨pc, run.2.symm⟩

lemma of_run_push {e s s' xs p} (h : Ninst.Run e s (push xs p) s') :
    Devm.PushBurn [xs.toB256] s s' := by
  rcases h with ⟨xl, _, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at run
  exact Devm.pushBurn_of_run run.2.symm

/-- A successful `push` run, as the executable equation the `Hinv` instance
proofs consume.  This is where the driver's step-outcome shape is unwound, once,
for every push-shaped instance. -/
lemma Ninst.run_push_eq {e : Sevm} {s s' : Devm} {xs : Bytes} {le : xs.length ≤ 32}
    (h : Ninst.Run e s (.push xs le) s') :
    (do let d ← chargeGas (if xs = [] then gBase else gVerylow) s
        d.push xs.toB256) = .ok s' := by
  rcases h with ⟨xl, -, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at run
  exact run.2.symm

lemma of_run_pushB256 {e s s' x} (h : Ninst.Run e s (pushB256 x) s') :
    Devm.PushBurn [x] s s' := by
  have h' := of_run_push h
  rwa [Bytes.toB256_sig, B256.toB256_toBytes] at h'

lemma of_run_pop {e : Sevm} {s s' : Devm} (h : Ninst.Run e s pop s') :
    ∃ x, Devm.PopBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop s with _ | ⟨x, s₂⟩ <;> simp [hp] at h1
  subst h1
  exact ⟨x, Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp) (Devm.burn_of_chargeGas h2)⟩

lemma of_run_dup {e : Sevm} {s s' : Devm} {n : Fin 16} (h : Ninst.Run e s (dup n) s') :
    ∃ x, s.stack[n.val]? = some x ∧ Devm.PushBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · rename_i x hx
    refine ⟨x, ?_, Devm.pushBurn_of_burn_of_push hb (Devm.push_of_push h2)⟩
    rw [hb.stack]; exact hx

lemma of_run_swap {e : Sevm} {s s' : Devm} {n : Fin 16} (h : Ninst.Run e s (swap n) s') :
    List.swap s.stack n.val = some s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · rename_i stk hstk
    injection h2 with eq; subst eq
    rw [hb.stack]; exact hstk

lemma of_run_caller {e : Sevm} {s s' : Devm} (h : Ninst.Run e s caller s') :
    Devm.PushBurn [e.caller.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_callvalue {e : Sevm} {s s' : Devm} (h : Ninst.Run e s callvalue s') :
    Devm.PushBurn [e.value] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_mstore {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mstore s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨i, s₁⟩, h1, run'⟩
  rcases of_bind_eq_ok run' with ⟨⟨v, s₂⟩, h2, run''⟩
  rcases of_bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  refine ⟨x, v, ?_⟩
  have hp := (Devm.pop_append p1 p2).stack
  rw [← eq]
  rw [show (Devm.memWrite s₃ i v.toBytes).stack = s₃.stack from rfl, ← hb.stack]
  exact hp

lemma Devm.pop_of_popN {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) :
    l.length = n ∧ Devm.Pop l devm devm' := by
  induction n generalizing devm l with
  | zero =>
    rw [Devm.popN_def] at hp
    injection hp with eq
    injection eq with eq1 eq2
    subst eq1; subst eq2
    refine ⟨rfl, ?_⟩
    constructor <;> simp [Devm.Rels.eq, Stack.Pop, Split]
  | succ n ih =>
    rw [Devm.popN_def] at hp
    rcases of_bind_eq_ok hp with ⟨⟨x, devm1⟩, hp1, hp2⟩
    rcases of_bind_eq_ok hp2 with ⟨⟨xs, devm2⟩, hp3, hp4⟩
    injection hp4 with eq
    injection eq with eq1 eq2
    subst eq1; subst eq2
    rcases ih hp3 with ⟨h_len, h_pop⟩
    refine ⟨by simp [h_len], Devm.pop_append (Devm.pop_of_pop hp1) h_pop⟩

lemma of_run_sstore {e : Sevm} {s s' : Devm} (h : Ninst.Run e s sstore s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨_, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
  rcases of_bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
  rcases of_bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
  rcases of_bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
  rcases of_bind_eq_ok run₇ with ⟨_, h8, h9⟩
  have hp := (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2)).stack
  have hb := Devm.burn_of_chargeGas h7
  have h_s₃ : s₃.stack = s₂.stack := by
    injection h4 with eq
    split at eq <;> (injection eq with eq _; subst eq; rfl)
  have h_s₄ : s₄.stack = s₃.stack := by
    injection h6 with eq; rw [← eq]
    rfl
  injection h9 with eq
  refine ⟨x, y, ?_⟩
  rw [← eq]
  show Stack.Pop [x, y] s.stack s₅.stack
  rw [← hb.stack, h_s₄, h_s₃]
  exact hp

lemma of_run_calldatacopy {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popToNat h3 with ⟨z, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  refine ⟨x, y, z, ?_⟩
  have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  rw [← eq]
  show Stack.Pop [x, y, z] s.stack s₄.stack
  rw [← hb.stack]
  exact hp

lemma of_run_singleton {e s i s'} (h : Line.Run e s [i] s') : Ninst.Run e s i s' := by
  rcases Line.of_run_cons h with ⟨_, hrun, hnil⟩
  cases hnil; exact hrun

lemma of_run_calldataload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldataload s') :
    ∃ x y, Stack.Diff [x] [y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  have hpop := Devm.pop_of_pop h1
  have hb := Devm.burn_of_chargeGas h2
  obtain ⟨val, hpush⟩ : ∃ val, Devm.Push [val] s₂ s' := ⟨_, Devm.push_of_push run₂⟩
  refine ⟨si, val, s₁.stack, hpop.stack, ?_⟩
  rw [show s₁.stack = s₂.stack from hb.stack]
  exact hpush.stack

lemma Devm.memRead_stack (devm : Devm) (i n : Nat) :
    (devm.memRead i n).2.stack = devm.stack := rfl

lemma of_run_kec {e : Sevm} {s s' : Devm} (h : Ninst.Run e s kec s') :
    ∃ x y z, Stack.Diff [x, y] [z] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  have hb := Devm.burn_of_chargeGas h3
  obtain ⟨val, hpush⟩ : ∃ val, Devm.Push [val] (s₃.memRead mi sz).2 s' :=
    ⟨_, Devm.push_of_push run₃⟩
  refine ⟨x, y, val, s₂.stack, (Devm.pop_append p1 p2).stack, ?_⟩
  rw [show s₂.stack = s₃.stack from hb.stack, ← Devm.memRead_stack s₃ mi sz]
  exact hpush.stack

lemma of_run_log {e : Sevm} {s s' : Devm} {n : Fin 5} (h : Ninst.Run e s (log n) s') :
    ∃ zs, zs.length = n.val + 2 ∧ Stack.Pop zs s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases of_bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases of_bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases of_bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases of_bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popN h3 with ⟨h_len, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases h_mem : Devm.memRead s₄ mi sz with ⟨data, s₅⟩
  rw [h_mem] at run₅
  injection run₅ with eq
  have h_s₅ : s₅.stack = s₄.stack := by
    simp only [Devm.memRead] at h_mem
    rcases h_read : s₄.memory.read mi sz with ⟨val, mem⟩
    rw [h_read] at h_mem
    injection h_mem with _ h_devm
    rw [← h_devm]; rfl
  refine ⟨x :: y :: topics, by simp [h_len], ?_⟩
  have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  rw [← eq]
  show Stack.Pop (x :: y :: topics) s.stack s₅.stack
  rw [h_s₅, ← hb.stack]
  exact hp

lemma Stack.swapCore_of_swap {n} {xxs yys : Stack} (h : Swap n xxs yys) :
    ∃ x y xs ys, xxs = x :: xs ∧ yys = y :: ys ∧ SwapCore x y n xs ys := by
  cases xxs; cases h; cases yys; cases h; refine ⟨_, _, _, _, rfl, rfl, h⟩

lemma Stack.swapCore_zero {x y s} : SwapCore x y 0 (y :: s) (x :: s) := by simp [SwapCore]

lemma Stack.swapCore_succ {n x y z s s'} :
    SwapCore x z n s s' → SwapCore x z (n + 1) (y :: s) (y :: s') := by simp [SwapCore]

lemma Stack.swapCore_getElem_set {x y : B256} {n : Nat} {xs xs' : Stack}
    (h : SwapCore x y n xs xs') (t : Stack) :
    (xs ++ t)[n]? = some y ∧ (xs ++ t).set n x = xs' ++ t := by
  induction n generalizing xs xs' with
  | zero =>
    cases xs; cases h; cases xs'; cases h
    rcases h with ⟨hx, hy, hl⟩
    subst hx; subst hy; subst hl
    constructor <;> rfl
  | succ n ih =>
    cases xs; cases h; cases xs'; cases h
    rcases h with ⟨hz, h⟩
    subst hz
    rcases ih h with ⟨h1, h2⟩
    constructor
    · simpa using h1
    · simp only [List.cons_append, List.set_cons_succ]
      rw [h2]

lemma Stack.prefix_of_swap {n} {xs xs' stk stk' : Stack} :
    Swap n xs xs' → List.swap stk n = some stk' → (xs <<+ stk) → (xs' <<+ stk') := by
  intro h0 h1 h2
  rcases swapCore_of_swap h0 with ⟨x, y, xs₀, ys₀, hxs, hys, hc⟩
  subst hxs; subst hys
  rcases h2 with ⟨t, h2⟩
  rw [show stk = (x :: xs₀) ++ t from h2] at h1
  rcases swapCore_getElem_set hc t with ⟨hget, hset⟩
  simp only [List.cons_append, List.swap, hget, hset] at h1
  injection h1 with h1
  refine ⟨t, ?_⟩
  rw [← h1]
  rfl

lemma Stack.nth_getElem {n : Nat} {x : B256} {xs ys : Stack}
    (h : Nth n x xs) (h' : xs <<+ ys) : ys[n]? = some x := by
  revert h'
  induction h generalizing ys with
  | head z zs =>
    intro h'
    rcases h' with ⟨t, h'⟩
    rw [show ys = (z :: zs) ++ t from h']; rfl
  | tail m z w zs h ih =>
    intro h'
    rcases h' with ⟨t, h'⟩
    rw [show ys = (w :: zs) ++ t from h']
    simp only [List.cons_append, List.getElem?_cons_succ]
    exact ih ⟨t, rfl⟩

lemma prefix_of_diffBurn_one (v : B256 → B256) {x xs} {s s' : Devm} :
    (∃ x', Devm.DiffBurn [x'] [v x'] s s') →
    (x :: xs <<+ s.stack) → (v x :: xs <<+ s'.stack) := by show_prefix_one

lemma prefix_of_diffBurn_two (v : B256 → B256 → B256) {x y xs} {s s' : Devm} :
    (∃ x' y', Devm.DiffBurn [x', y'] [v x' y'] s s') →
    (x :: y :: xs <<+ s.stack) → (v x y :: xs <<+ s'.stack) := by show_prefix_two

lemma prefix_of_not {e} {x xs} {s s' : Devm} :
    Ninst.Run e s not s' → (x :: xs <<+ s.stack) → ((~~~ x) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_one (~~~ ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyUnary run

lemma prefix_of_iszero {e} {x xs} {s s' : Devm} :
    Ninst.Run e s iszero s' → (x :: xs <<+ s.stack) → ((x =? 0) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_one (· =? 0) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyUnary run

lemma prefix_of_eq {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s eq s' → (x :: y :: xs <<+ s.stack) → ((x =? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.eqCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_lt {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s lt s' → (x :: y :: xs <<+ s.stack) → ((x <? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.ltCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_gt {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s gt s' → (x :: y :: xs <<+ s.stack) → ((x >? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.gtCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_shl {e} {x y : B256} {xs} {s s' : Devm} :
    Ninst.Run e s shl s' → (x :: y :: xs <<+ s.stack) → (y <<< x.toNat :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (fun x y => y <<< x.toNat) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_shr {e} {x y : B256} {xs} {s s' : Devm} :
    Ninst.Run e s shr s' → (x :: y :: xs <<+ s.stack) → (y >>> x.toNat :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (fun x y => y >>> x.toNat) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_or {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s or s' → (x :: y :: xs <<+ s.stack) → ((x ||| y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.or ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_and {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s and s' → (x :: y :: xs <<+ s.stack) → ((x &&& y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.and ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_add {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s add s' → (x :: y :: xs <<+ s.stack) → ((x + y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· + ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_sub {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s sub s' → (x :: y :: xs <<+ s.stack) → ((x - y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· - ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_push {xs ys} {s s' : Devm} :
    Devm.PushBurn xs s s' → (ys <<+ s.stack) → ((xs ++ ys) <<+ s'.stack) :=
  λ h0 h1 => append_pref h0.stack h1

lemma prefix_of_pop {y : B256} {xs} {s s' : Devm} :
    (∃ x, Devm.PopBurn [x] s s') → (y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h h'; rcases h with ⟨x, hx⟩
  have h_eq : y = x :=
    (List.of_cons_pref_of_cons_pref h' (pref_of_split hx.stack)).left
  rw [h_eq] at h'
  exact of_append_pref hx.stack h'

lemma prefix_of_mstore {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s mstore s' → (x :: y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_mstore h0 with ⟨x', y', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact of_append_pref h2 h1

lemma prefix_of_sstore {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s sstore s' → (x :: y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_sstore h0 with ⟨x', y', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact of_append_pref h2 h1

lemma prefix_of_calldatacopy {e} {x y z xs} {s s' : Devm} :
    Ninst.Run e s calldatacopy s' → (x :: y :: z :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_calldatacopy h0 with ⟨x', y', z', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, _⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

lemma prefix_of_calldataload {e} {x xs} {s s' : Devm} :
    Ninst.Run e s calldataload s' → (x :: xs <<+ s.stack) → ∃ z, z :: xs <<+ s'.stack := by
  intro h0 h1
  rcases of_run_calldataload h0 with ⟨x', y', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  rw [hx] at h1
  exact ⟨y', append_pref h3 (of_append_pref h2 h1)⟩

lemma prefix_of_kec {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s kec s' → (x :: y :: xs <<+ s.stack) → ∃ z, z :: xs <<+ s'.stack := by
  intro h0 h1
  rcases of_run_kec h0 with ⟨x', y', z', stk, h2, h3⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact ⟨z', append_pref h3 (of_append_pref h2 h1)⟩

lemma prefix_of_cdl {e n xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s (cdl n) s' → ∃ z, z :: xs <<+ s'.stack := by
  intro h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s₁, h_push, h_rest⟩
  rcases Line.of_run_cons h_rest with ⟨s₂, h_cdl, h_nil⟩
  cases h_nil
  have h1 : n :: xs <<+ s₁.stack := prefix_of_push (of_run_pushB256 h_push) h_pfx
  exact prefix_of_calldataload h_cdl h1

lemma of_run_sload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s sload s') :
    ∃ x, Stack.Diff [x] [Devm.getStorVal s e.currentTarget x] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases of_bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  have hpop := Devm.pop_of_pop h1
  have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
  refine ⟨key, s₁.stack, hpop.stack, ?_⟩
  suffices H : ∀ (d : Devm) (c : Nat),
      Devm.getStor s₁ = Devm.getStor d → s₁.stack = d.stack →
      (chargeGas c d >>= fun y => Devm.push (Devm.getStorVal y e.currentTarget key) y) = .ok s' →
      Stack.Push [Devm.getStorVal s e.currentTarget key] s₁.stack s'.stack by
    split at run₁
    · exact H s₁ gasWarmAccess rfl rfl run₁
    · exact H (addAccessedStorageKey s₁ e.currentTarget key) gasColdSload
        (@addAccessedStorageKey_getStor s₁ e.currentTarget key).symm rfl run₁
  intro d c hgs hst run'
  rcases of_bind_eq_ok run' with ⟨s₂, h2, run₂⟩
  have hpush := Devm.push_of_push run₂
  have hstk : d.stack = s₂.stack := (Devm.burn_of_chargeGas h2).stack
  have e2 : Devm.getStor d = Devm.getStor s₂ := chargeGas_getStor_eq h2
  have hval : Devm.getStorVal s₂ e.currentTarget key
      = Devm.getStorVal s e.currentTarget key := by
    show (Devm.getStor s₂ e.currentTarget).get key =
      (Devm.getStor s e.currentTarget).get key
    rw [← e2, ← hgs, ← e1]
  rw [hst, hstk, ← hval]
  exact hpush.stack

lemma prefix_of_sload {e x xs} {s s' : Devm} :
    Ninst.Run e s sload s' → (x :: xs <<+ s.stack) →
    ∃ y, (y :: xs <<+ s'.stack) ∧ y = Devm.getStorVal s e.currentTarget x := by
  intro h0 h1
  rcases of_run_sload h0 with ⟨x', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  exact ⟨_, append_pref h3 (of_append_pref h2 h1), rfl⟩

lemma Line.spx_scheme {e s' i l xs xs' ys}
    (h : ∀ s0 s1, Ninst.Run e s0 i s1 → (xs <<+ s0.stack) → (xs' <<+ s1.stack))
    (h' : ∀ s : Devm, (xs' <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) :
    ∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (i :: l) s' → (ys <<+ s'.stack) := by
  intros s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h' s_mid (h _ _ h_head h_pfx) h_tail

lemma Line.spx_push {e : Sevm} {s' l bs p xs ys} :
    (∀ s : Devm, (bs.toB256 :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (push bs p :: l) s' → (ys <<+ s'.stack)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_push h_head) h_pfx

lemma Line.spx_pushB256 {e : Sevm} {s' l x xs ys} :
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (pushB256 x :: l) s' → (ys <<+ s'.stack)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_pushB256 h_head) h_pfx

lemma Line.spx_mstore {e : Sevm} {s' l x y xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (mstore :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_mstore

lemma Line.spx_sstore {e : Sevm} {s' l x y xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (sstore :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_sstore

lemma Line.spx_dup {e s' l xs ys} {n : Fin 16} (x) :
    Stack.Nth n.val x xs →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (dup n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_nth; apply Line.spx_scheme
  intros s0 s1 h_step h_pfx
  rcases of_run_dup h_step with ⟨w, h_get, h_pb⟩
  rw [Stack.nth_getElem h_nth h_pfx] at h_get
  injection h_get with h_get
  rw [h_get]
  apply prefix_of_push h_pb h_pfx

lemma Line.spx_log (zs : Stack) {e s' l xs ys} {n : Fin 5} :
    zs.length = n.val + 2 →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (zs ++ xs <<+ s.stack) → Line.Run e s (log n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_len; apply Line.spx_scheme
  intros s₀ s₁ h_step h_pfx
  rcases of_run_log h_step with ⟨zs', h_len', h_pop⟩
  have h_zs : (zs <<+ s₀.stack) := @pref_trans _ zs (zs ++ xs) _ ⟨xs, rfl⟩ h_pfx
  have h_zs' : (zs' <<+ s₀.stack) := pref_of_split h_pop
  cases List.pref_unique (Eq.trans h_len h_len'.symm) h_zs h_zs'
  exact of_append_pref h_pop h_pfx

lemma Line.spx_swap (xs') {e s' l xs ys} {n : Fin 16} :
    Stack.Swap n.val xs xs' →
    (∀ s : Devm, (xs' <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (swap n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_swap; apply Line.spx_scheme
  intros s0 s1 h_step
  exact Stack.prefix_of_swap h_swap (of_run_swap h_step)

lemma Line.spx_iszero {e s' l} {x} {xs ys} :
    (∀ s : Devm, ((x =? 0) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (iszero :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_iszero

lemma Line.spx_pop {e : Sevm} {s' l x xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (pop :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step
  exact prefix_of_pop (of_run_pop h_step)

lemma Line.spx_eq {e s' l x y xs ys} :
    (∀ s : Devm, ((x =? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (eq :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_eq

lemma Line.spx_lt {e s' l x y xs ys} :
    (∀ s : Devm, ((x <? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (lt :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_lt

lemma Line.spx_gt {e s' l x y xs ys} :
    (∀ s : Devm, ((x >? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (gt :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_gt

lemma Line.spx_sub {e s' l x y xs ys} :
    (∀ s : Devm, ((x - y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (sub :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_sub

lemma Line.spx_not {e s' l x xs ys} :
    (∀ s : Devm, (~~~ x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (not :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_not

lemma Line.spx_or {e s' l x y xs ys} :
    (∀ s : Devm, ((x ||| y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (or :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_or

lemma Line.spx_and {e s' l x y xs ys} :
    (∀ s : Devm, ((x &&& y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (and :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_and

lemma Line.spx_shl {e s' l} {x y : B256} {xs ys} :
    (∀ s : Devm, (y <<< x.toNat :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (shl :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_shl

lemma Line.spx_shr {e s' l} {x y : B256} {xs ys} :
    (∀ s : Devm, (y >>> x.toNat :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (shr :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_shr

lemma Line.spx_add {e s' l x y xs ys} :
    (∀ s : Devm, ((x + y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (add :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_add

lemma Line.spx_caller {e : Sevm} {s' l xs ys} :
    (∀ s : Devm, (e.caller.toB256 :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (caller :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step h_pfx
  apply prefix_of_push (of_run_caller h_step) h_pfx

lemma Line.spx_callvalue {e : Sevm} {s' l xs ys} :
    (∀ s : Devm, (e.value :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (callvalue :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step h_pfx
  apply prefix_of_push (of_run_callvalue h_step) h_pfx

lemma Line.spx_calldatacopy {e : Sevm} {s' l x y z xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: z :: xs <<+ s.stack) → Line.Run e s (calldatacopy :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_calldatacopy

lemma Line.spx_unwrap {e xs} {s' : Devm} :
    ∀ s : Devm, (xs <<+ s.stack) → Line.Run e s [] s' → (xs <<+ s'.stack) := by
  intros _ h0 h1; cases h1; apply h0


lemma memRead_getBal_eq {x n : Nat} {devm devm' : Devm} {value : Bytes} (h : devm.memRead x n = ⟨value, devm'⟩) (a : Adr) : devm'.getBal a = devm.getBal a := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

/-- Successful-run observation invariant retained as the public projection of
the canonical regular-instruction effect theorems. -/
def Rinst.Inv {ξ : Type} (f : Devm → ξ) (r : Rinst) : Prop :=
  ∀ {pc sevm pre post}, Rinst.run ⟨pc, sevm, pre⟩ r = (.ok post) → f pre = f post

lemma Rinst.preserves_bal {r} : Rinst.Inv Devm.getBal r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf; exact funext hf.getBal_eq
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact congrArg (fun s => s.bal) hf.state
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs ht; rw [hrun] at hf; exact funext hf.getBal

lemma memRead_getStor_eq {x n : Nat} {devm devm' : Devm} {value : Bytes}
    (h : devm.memRead x n = ⟨value, devm'⟩) :
    Devm.getStor devm' = Devm.getStor devm := by
  simp only [Devm.memRead] at h
  rcases h_read : devm.memory.read x n with ⟨val, mem⟩
  rw [h_read] at h
  injection h with _ h_devm
  rw [← h_devm]
  rfl

lemma Rinst.preserves_stor {r} (h_not_sstore : r ≠ Rinst.sstore) : Rinst.Inv Devm.getStor r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact congrArg (fun s => fun a => (s.get a).stor) hf.state
  · have hf := Rinst.run_instructionFrame pc sevm pre r h_not_sstore ht; rw [hrun] at hf
    exact funext (Devm.InstructionFrame.getStor hf)

class Rinst.Hinv {ξ : Type} (f : Devm → ξ) (o : Rinst) where (inv : Rinst.Inv f o)

instance {ξ : Type} (f : Devm → ξ) (o : Rinst) [Rinst.Hinv f o] :
    Ninst.Hinv f (Ninst.reg o) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
  exact Rinst.Hinv.inv run.2.symm
⟩

instance {o : Rinst} : Rinst.Hinv Devm.getBal o := ⟨Rinst.preserves_bal⟩

instance {o : Rinst} : Rinst.Hinv Devm.getCode o := ⟨by
  intro pc sevm pre post run
  funext a
  exact (Rinst.preserves_getCode run a).symm⟩

syntax "show_hinv_stor" : tactic
macro_rules
  | `(tactic| show_hinv_stor) =>
    `(tactic| exact ⟨Rinst.preserves_stor (by intro; contradiction)⟩)


instance : Rinst.Hinv Devm.getStor Rinst.add := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mul := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sub := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.div := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sdiv := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.smod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.addmod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mulmod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.exp := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.signextend := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.lt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.slt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sgt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.eq := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.iszero := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.and := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.or := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.xor := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.not := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.byte := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.shr := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.shl := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sar := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.clz := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.kec := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.address := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.balance := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.origin := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.caller := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.callvalue := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldataload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldatasize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldatacopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.codesize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.codecopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gasprice := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodesize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodecopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.retdatasize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.retdatacopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodehash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blockhash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.coinbase := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.timestamp := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.number := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.prevrandao := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gaslimit := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.chainid := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.selfbalance := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.basefee := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blobhash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blobbasefee := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.pop := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mstore := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mstore8 := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.tload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.tstore := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mcopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.pc := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.msize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gas := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.dup n) := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.swap n) := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.log n) := by show_hinv_stor

/-! ## §1 AdrSet non-membership helpers -/

namespace AdrSet

theorem not_mem_insert {a b : Adr} {s : AdrSet} (hne : a ≠ b) (hs : a ∉ s) :
    a ∉ s.insert b := by
  simp only [Std.HashSet.mem_insert, not_or]
  exact ⟨by simpa using Ne.symm hne, hs⟩

theorem not_mem_union {a : Adr} {m₁ m₂ : AdrSet} (h₁ : a ∉ m₁) (h₂ : a ∉ m₂) :
    a ∉ m₁.union m₂ := by
  intro h
  have hm : a ∈ m₁ ∨ a ∈ m₂ := Std.HashSet.mem_union_iff.mp h
  exact hm.elim h₁ h₂

theorem not_mem_empty {a : Adr} {c : Nat} :
    a ∉ (Std.HashSet.emptyWithCapacity c : AdrSet) := by
  simp

end AdrSet

/-! ## §2 The NoDel invariant -/

-- rfl-bridge between the Devm-level and State-level code projections.
lemma Devm.getCode_state (d : Devm) (a : Adr) :
    d.getCode a = d.state.getCode a := rfl

-- The frame-level invariant. The `code` conjunct is the fuel for the
-- CREATE collision guards; it is transported by the PROVED getCode ladder,
-- never re-proved here.
structure Devm.NoDel (wa : Adr) (d : Devm) : Prop where
  (atd  : wa ∉ d.accountsToDelete)
  (ca   : wa ∉ d.createdAccounts)
  (code : (d.getCode wa).toList ≠ [])

-- The message-level invariant (a fresh frame starts with atd = ∅,
-- ca = msg.benv.createdAccounts, state = msg.benv.state; see initDevm,
-- jaune Execution.lean:2657).
structure Msg.NoDel (wa : Adr) (msg : Msg) : Prop where
  (ca   : wa ∉ msg.benv.createdAccounts)
  (code : (msg.benv.state.getCode wa).toList ≠ [])

-- Result-level invariants: error payloads carry live atd/ca (handleError
-- can resurrect them into ok results), so they must be covered.
def Execution.NoDel (wa : Adr) : Execution → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, d⟩ => Devm.NoDel wa d

-- Msg-level results (`processMessage`-shaped): the error payload carries
-- only createdAccounts + state (no atd; consumers merge it via
-- liftToExecution, keeping the parent's atd).
def MsgResult.NoDel (wa : Adr) :
    Except (EvmError × State × AdrSet × Tra) Devm → Prop
  | .ok d => Devm.NoDel wa d
  | .error ⟨_, st, ca, _⟩ => wa ∉ ca ∧ (st.getCode wa).toList ≠ []

-- The sub-execution oracle invariant threaded through the Exec induction
-- (result-shaped like Xlot.InvGetCode, Common.lean:4076; the former
-- Xlot.InvNof mirror in Solvent.lean was replaced by Exec.balance_effect).
def Xlot.InvNoDel (wa : Adr) : Xlot → Prop
  | .none => True
  | .some ⟨evm_, exn_⟩ => Devm.NoDel wa evm_.dyna → Execution.NoDel wa exn_

/-! ## §3 Proved transports -/

-- Transport NoDel across a step that moves neither set nor wa's code.
lemma Devm.NoDel.of_eqs {wa : Adr} {d d' : Devm}
    (hs : Devm.delSets d = Devm.delSets d') (hc : d.getCode wa = d'.getCode wa)
    (h : Devm.NoDel wa d) : Devm.NoDel wa d' := by
  have h1 : d.accountsToDelete = d'.accountsToDelete := congrArg Prod.fst hs
  have h2 : d.createdAccounts = d'.createdAccounts := congrArg Prod.snd hs
  exact ⟨h1 ▸ h.atd, h2 ▸ h.ca, hc ▸ h.code⟩

-- A fresh frame satisfies NoDel (initDevm: atd := ∅, ca := benv.ca).
lemma Msg.NoDel.initDevm {wa : Adr} {msg : Msg}
    (h : Msg.NoDel wa msg) : Devm.NoDel wa (initDevm msg) :=
  ⟨AdrSet.not_mem_empty, h.ca, h.code⟩

-- Rollback keeps atd/ca and installs the given state.
lemma Devm.NoDel.rollback {wa : Adr} {d : Devm} {st : State} {tra : Tra}
    (h_atd : wa ∉ d.accountsToDelete) (h_ca : wa ∉ d.createdAccounts)
    (h_code : (st.getCode wa).toList ≠ []) :
    Devm.NoDel wa (d.rollback st tra) :=
  ⟨h_atd, h_ca, h_code⟩

-- handleError shuffles error payloads into ok results without touching
-- the sets (jaune Execution.lean:2692-2701).
lemma handleError_noDel {wa : Adr} {exn : Execution}
    (h : Execution.NoDel wa exn) :
    MsgResult.NoDel wa (executeCode.handleError exn) := by
  cases exn with
  | ok d => exact h
  | error p =>
    rcases p with ⟨err, d⟩
    have hd : Devm.NoDel wa d := h
    cases err <;>
      first
        | exact ⟨hd.atd, hd.ca, hd.code⟩
        | exact ⟨hd.ca, hd.code⟩

/-! ## §4 Plumbing -/

-- The create-guard bridge: an address whose account has size-0 code cannot be the code-bearing wa.
lemma ne_wa_of_code_size_zero {st : State} {wa b : Adr}
    (hwa : (st.getCode wa).toList ≠ []) (hb : (st.get b).code.size = 0) :
    b ≠ wa := by
  intro h
  subst h
  have h_empty : (st.get b).code.toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp [hb]
  unfold State.getCode at hwa
  rw [h_empty] at hwa
  exact hwa rfl

-- Same bridge via the collision predicate used by `processMessageCall.create`.
lemma ne_wa_of_not_hasCodeOrNonce {st : State} {wa ct : Adr}
    (hwa : (st.getCode wa).toList ≠ [])
    (h : accountHasCodeOrNonce st ct = false) : ct ≠ wa := by
  intro heq
  subst heq
  unfold accountHasCodeOrNonce at h
  rw [Bool.or_eq_false_iff] at h
  have h_empty_not := h.2
  have h_empty : (st.getCode ct).isEmpty = true := by
    simp at h_empty_not
    exact h_empty_not
  have hb : (st.getCode ct).size = 0 := by
    unfold ByteArray.isEmpty at h_empty
    simp at h_empty
    simpa using congrArg ByteArray.size h_empty
  have h_empty_list : (st.getCode ct).toList = [] := by
    unfold ByteArray.toList
    unfold ByteArray.toList.loop
    simp [hb]
  rw [h_empty_list] at hwa
  exact hwa rfl

lemma State.get_set_self {w : Jaune.State} {a : Adr} {ac : Acct} :
    (w.set a ac).get a = ac := by
  unfold State.set State.get
  split_ifs with h
  · rw [Std.TreeMap.getD_erase]; simp; exact h.symm
  · rw [Std.TreeMap.getD_insert]; simp

lemma State.get_set_ne {w : Jaune.State} {a a' : Adr} {ac : Acct} (h : a' ≠ a) :
    (w.set a' ac).get a = w.get a := by
  unfold State.set State.get
  have hc : compare a' a ≠ Ordering.eq := by
    intro hcc; exact h (compare_eq_iff_eq.mp hcc)
  split_ifs with hv
  · rw [Std.TreeMap.getD_erase]; simp [hc]
  · rw [Std.TreeMap.getD_insert]; simp [hc]

lemma State.set_bal {st : Jaune.State} {a : Adr} {ac : Acct}
    (h : ac.bal = (st.get a).bal) : (st.set a ac).bal = st.bal := by
  funext b
  by_cases hb : b = a
  · subst hb
    show ((st.set b ac).get b).bal = (st.get b).bal
    rw [State.get_set_self]
    exact h
  · show ((st.set a ac).get b).bal = (st.get b).bal
    rw [State.get_set_ne (fun hc => hb hc.symm)]

lemma State.setStor_bal {st : Jaune.State} {a : Adr} {s : Stor} :
    (st.setStor a s).bal = st.bal := State.set_bal rfl

lemma State.incrNonce_bal {st : Jaune.State} {a : Adr} :
    (st.incrNonce a).bal = st.bal := State.set_bal rfl

lemma State.setCode_bal {st : Jaune.State} {a : Adr} {cd : ByteArray} :
    (st.setCode a cd).bal = st.bal := State.set_bal rfl

-- The create-seeding step: wa ∉ msg.benv.createdAccounts and code is untouched.
lemma Msg.NoDel.processCreateMessage_msg {wa : Adr} {msg : Msg}
    (h_ct : msg.currentTarget ≠ wa)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (processCreateMessage.msg msg) := by
  rcases h with ⟨hca, hcode⟩
  refine ⟨?_, ?_⟩
  · show wa ∉ msg.benv.createdAccounts.insert msg.currentTarget
    exact AdrSet.not_mem_insert (Ne.symm h_ct) hca
  · show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).getCode wa).toList ≠ []
    have h_get : ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa = msg.benv.state.get wa := by
      dsimp only [State.incrNonce, State.setStor]
      rw [State.get_set_ne h_ct, State.get_set_ne h_ct]
    show (((msg.benv.state.setStor msg.currentTarget .empty).incrNonce msg.currentTarget).get wa).code.toList ≠ []
    rw [h_get]
    exact hcode

-- Precompiles never touch the sets or code.
lemma executePrecomp_noDel {wa : Adr} {evm : Evm} {adr : Adr} {exn : Execution}
    (h_ex : executePrecomp evm adr = exn)
    (h : Devm.NoDel wa evm.dyna) : Execution.NoDel wa exn := by
  unfold executePrecomp at h_ex
  revert h_ex
  generalize h_res : precompileRun evm adr = res
  intro h_ex
  subst h_ex
  cases res
  · apply Devm.NoDel.of_eqs (d := evm.dyna)
    · rfl
    · rfl
    · exact h
  · apply Devm.NoDel.of_eqs (d := evm.dyna)
    · rfl
    · rfl
    · exact h

/-! ## §5 Instruction level -/

-- Helper lemmas for the EVM instructions delSets preservation.
lemma liftMach_delSets_of_ok {core : Mach → Footprint.Outcome Mach α}
    {d d' : Devm} {x : α} (h : liftMach core d = .ok (x, d')) :
    Devm.delSets d' = Devm.delSets d := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error err => simp [hc] at h
  | ok out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    rfl

lemma liftMach_delSets_of_error {core : Mach → Footprint.Outcome Mach α}
    {d : Devm} {err : EvmError × Devm} (h : liftMach core d = .error err) :
    Devm.delSets err.2 = Devm.delSets d := by
  unfold liftMach Footprint.liftOutcome at h
  cases hc : core d.mach with
  | error out =>
    simp [hc] at h
    rcases h with ⟨_, rfl⟩
    rfl
  | ok out => simp [hc] at h

lemma liftMachExecution_delSets_of_ok {core : Mach → Footprint.Outcome Mach Unit}
    {d d' : Devm} (h : liftMachExecution core d = .ok d') :
    Devm.delSets d' = Devm.delSets d := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · cases h
  · rename_i out heq
    cases h
    exact liftMach_delSets_of_ok heq

lemma liftMachExecution_delSets_of_error {core : Mach → Footprint.Outcome Mach Unit}
    {d : Devm} {err : EvmError × Devm} (h : liftMachExecution core d = .error err) :
    Devm.delSets err.2 = Devm.delSets d := by
  unfold liftMachExecution Footprint.toExecution at h
  split at h
  · rename_i e heq
    cases h
    exact liftMach_delSets_of_error heq
  · cases h

lemma Devm.pop_delSets_eq {x devm devm'} (h : Devm.pop devm = .ok ⟨x, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  simp only [Devm.pop_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma chargeGas_delSets_eq {cost devm devm'} (h : chargeGas cost devm = .ok devm') : Devm.delSets devm' = Devm.delSets devm := by
  simp only [chargeGas_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_eq {v devm devm'} (h : Devm.push v devm = .ok devm') : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMachExecution_delSets_of_ok (core := Mach.push v) h

lemma Devm.popToAdr_delSets_eq {devm devm' adr} (h : Devm.popToAdr devm = .ok ⟨adr, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMach_delSets_of_ok (core := Mach.popToAdr) h

lemma Devm.popToNat_delSets_eq {devm devm' n} (h : Devm.popToNat devm = .ok ⟨n, devm'⟩) : Devm.delSets devm' = Devm.delSets devm := by
  exact liftMach_delSets_of_ok (core := Mach.popToNat) h

lemma Rinst.inv_delSets {r : Rinst} : Rinst.Inv Devm.delSets r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf
    exact Prod.ext hf.accountsToDelete hf.createdAccounts
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc pre sevm; rw [hrun] at hf
    exact Prod.ext hf.accountsToDelete hf.createdAccounts
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs ht; rw [hrun] at hf; exact Devm.InstructionFrame.delSets hf

lemma chargeGas_delSets_err {cost devm err} (h : chargeGas cost devm = .error err) : Devm.delSets err.2 = Devm.delSets devm := by
  simp only [chargeGas_def] at h
  split at h <;> try contradiction
  cases h; rfl

lemma Devm.push_delSets_err {v devm err} (h : Devm.push v devm = Except.error err) : Devm.delSets err.2 = Devm.delSets devm := by
  exact liftMachExecution_delSets_of_error (core := Mach.push v) h

lemma Devm.popToAdr_delSets_err {devm err} (h : Devm.popToAdr devm = .error err) : Devm.delSets err.2 = Devm.delSets devm := by
  exact liftMach_delSets_of_error (core := Mach.popToAdr) h

-- Rinst execution preserves delSets on error results.
lemma Rinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {r : Rinst}
    {err : EvmError} {devm' : Devm}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = .error ⟨err, devm'⟩) :
    Devm.delSets devm' = Devm.delSets devm := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Prod.ext (by change devm.accountsToDelete = devm'.accountsToDelete; exact hf.accountsToDelete) (by change devm.createdAccounts = devm'.createdAccounts; exact hf.createdAccounts)).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact (Prod.ext (by change devm.accountsToDelete = devm'.accountsToDelete; exact hf.accountsToDelete) (by change devm.createdAccounts = devm'.createdAccounts; exact hf.createdAccounts)).symm
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf
    exact (Devm.InstructionFrame.delSets hf).symm

lemma Jinst.inv_delSets {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {pc' : Nat} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩)) :
    Devm.delSets devm' = Devm.delSets devm := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (Devm.InstructionFrame.delSets hf).symm

lemma Jinst.inv_delSets_err {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    {err : EvmError} {devm' : Devm}
    (run : Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩)) :
    Devm.delSets devm' = Devm.delSets devm := by
  have hf := Jinst.run_instructionFrame ⟨pc, sevm, devm⟩ j
  rw [run] at hf
  exact (Devm.InstructionFrame.delSets hf).symm

-- Halting/terminal instructions (Linst) preserve NoDel.
lemma Linst.dest_preserves_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {exn : Execution} (run : Linst.Run sevm devm .dest exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : devm.popToAdr <;> dsimp
  case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (Devm.popToAdr_delSets_err h1).symm (Devm.popToAdr_getCode_err h1 wa).symm h
  case ok res1 =>
    have h_acc : (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getCode wa = res1.2.getCode wa := by
      split
      · exact addAccessedAddress_getCode
      · rfl
    have h_acc_ds : Devm.delSets
        (if res1.1 ∉ res1.2.accessedAddresses then
          (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess)
        else (res1.2, gasSelfDestruct)).1 = Devm.delSets res1.2 := by
      split
      · rfl
      · rfl
    cases h2 : chargeGas (if ((if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧ ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount else (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).2) (if res1.1 ∉ res1.2.accessedAddresses then (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess) else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err => intro run; rw [← run]; exact Devm.NoDel.of_eqs (chargeGas_delSets_err h2).symm (chargeGas_getCode_err h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
    case ok res2 =>
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run; rw [← run]
        dsimp [assertDynamic, Except.assert] at h3
        split at h3
        · contradiction
        · simp only [Except.error.injEq] at h3; subst h3
          exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run; rw [← run]
          exact Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
        case some res3 =>
          have hd : Devm.NoDel wa res2 := Devm.NoDel.of_eqs (chargeGas_delSets_eq h2).symm (chargeGas_getCode_eq h2 wa).symm (Devm.NoDel.of_eqs h_acc_ds.symm h_acc.symm (Devm.NoDel.of_eqs (Devm.popToAdr_delSets_eq h1).symm (Devm.popToAdr_getCode_eq h1 wa).symm h))
          have h_sub : res3.getCode wa = res2.getCode wa := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none =>
              rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              change st.getCode wa = res2.getCode wa
              exact State.subBal_getCode h_st
          have h_sub_ds : Devm.delSets res3 = Devm.delSets res2 := by
            dsimp [Devm.subBal] at h4
            cases h_st : res2.state.subBal sevm.currentTarget (res1.2.getAcct sevm.currentTarget).bal
            case none => rw [h_st] at h4; contradiction
            case some st =>
              rw [h_st] at h4; dsimp at h4
              simp only [Option.some.injEq] at h4; subst h4
              rfl
          have hd3 : Devm.NoDel wa res3 := Devm.NoDel.of_eqs h_sub_ds.symm h_sub.symm hd
          by_cases h_if : sevm.currentTarget ∈ (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [h_if, if_pos]
            intro run; rw [← run]
            have h_ca_eq : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).createdAccounts = res3.createdAccounts := rfl
            have h_ca : sevm.currentTarget ∈ res3.createdAccounts := h_ca_eq ▸ h_if
            have h_ne : sevm.currentTarget ≠ wa := by
              intro heq; rw [heq] at h_ca
              exact hd3.ca h_ca
            constructor
            · exact AdrSet.not_mem_insert (Ne.symm h_ne) hd3.atd
            · exact hd3.ca
            · have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
              have h_set : ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0).getCode wa = (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa := by
                dsimp [Devm.setBal, Devm.getCode]; exact State.setBal_getCode _ _ _ _
              have h_code : (addAccountToDelete ((res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).setBal sevm.currentTarget 0) sevm.currentTarget).getCode wa = res3.getCode wa :=
                h_set.trans h_add
              rw [h_code]; exact hd3.code
          · simp only [h_if]
            intro run; rw [← run]
            constructor
            · exact hd3.atd
            · exact hd3.ca
            · have h_add : (res3.addBal res1.1 (res1.2.getAcct sevm.currentTarget).bal).getCode wa = res3.getCode wa := by
                dsimp [Devm.addBal, Devm.getCode]; exact State.addBal_getCode res3.state _ _ _
              rw [h_add]; exact hd3.code

theorem Linst.run_noDel {wa : Adr} {sevm : Sevm} {devm : Devm}
    {l : Linst} {exn : Execution} (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · exact Linst.dest_preserves_noDel run h
  · have hf := Linst.run_instructionFrame sevm devm l h_not_dest
    rw [run] at hf
    cases exn <;>
      exact Devm.NoDel.of_eqs (Devm.InstructionFrame.delSets hf) (hf.getCode wa) h

lemma Linst.inv_noDel {wa : Adr} {sevm : Sevm} {devm : Devm} {l : Linst}
    {exn : Execution}
    (run : Linst.Run sevm devm l exn)
    (h : Devm.NoDel wa devm) : Execution.NoDel wa exn := by
  exact Linst.run_noDel run h

lemma Msg.NoDel.benvAfterTransfer_err {wa : Adr} {msg : Msg}
    {x : EvmError × State × AdrSet × Tra}
    (h_run : msg.benvAfterTransfer = .error x)
    (h : Msg.NoDel wa msg) : wa ∉ x.2.2.1 ∧ (x.2.1.getCode wa).toList ≠ [] := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_pos h_stv] at h_run
    cases h_sub : msg.benv.subBal msg.caller msg.value
    · rw [h_sub] at h_run
      simp only [Except.error.injEq, Option.toExcept, Except.bind, bind] at h_run
      subst h_run
      exact ⟨h.ca, h.code⟩
    · rw [h_sub] at h_run
      dsimp [Option.toExcept] at h_run
      contradiction
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_neg h_stv] at h_run
    contradiction

lemma chargeCodeGas_delSets_ok {rules : ForkRules} {d d' : Devm}
    (h : processCreateMessage.chargeCodeGas rules d = .ok d') :
    Devm.delSets d' = Devm.delSets d := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h
  · rcases of_bind_eq_ok h with ⟨d1, h_charge, h_rest⟩
    split_ifs at h_rest
    cases h_rest
    exact chargeGas_delSets_eq h_charge

lemma chargeCodeGas_delSets_err {rules : ForkRules} {d d' : Devm} {err : EvmError}
    (h : processCreateMessage.chargeCodeGas rules d = .error ⟨err, d'⟩) :
    Devm.delSets d' = Devm.delSets d := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · cases h; rfl
  · rcases hcg : chargeGas _ d with ⟨e, dd⟩ | dd
    · rw [hcg] at h
      dsimp only [Bind.bind, Except.bind] at h
      cases h
      exact chargeGas_delSets_err hcg
    · rw [hcg] at h
      dsimp only [Bind.bind, Except.bind] at h
      split_ifs at h
      cases h; exact chargeGas_delSets_eq hcg

lemma Devm.push_noDel {wa : Adr} {x : B256} {d : Devm} {exn : Execution}
    (heq : Devm.push x d = exn) (h : Devm.NoDel wa d) : Execution.NoDel wa exn := by
  subst heq
  cases hp : Devm.push x d with
  | error err =>
    have hd := Devm.push_delSets_err hp
    refine ⟨?_, ?_, (Devm.push_getCode_err hp wa) ▸ h.code⟩
    · rw [show err.2.accountsToDelete = d.accountsToDelete from congrArg Prod.fst hd]
      exact h.atd
    · rw [show err.2.createdAccounts = d.createdAccounts from congrArg Prod.snd hd]
      exact h.ca
  | ok d' =>
    have hd := Devm.push_delSets_eq hp
    refine ⟨?_, ?_, (Devm.push_getCode_eq hp wa) ▸ h.code⟩
    · rw [show d'.accountsToDelete = d.accountsToDelete from congrArg Prod.fst hd]
      exact h.atd
    · rw [show d'.createdAccounts = d.createdAccounts from congrArg Prod.snd hd]
      exact h.ca

lemma incorporateChildOnError_noDel {wa : Adr} {parent child : Devm} {rd : Bytes}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnError parent child rd) :=
  ⟨hp_atd, hc.ca, hc.code⟩

lemma incorporateChildOnSuccess_noDel {wa : Adr} {parent child : Devm} {rd : Bytes}
    (hp_atd : wa ∉ parent.accountsToDelete) (hc : Devm.NoDel wa child) :
    Devm.NoDel wa (incorporateChildOnSuccess parent child rd) :=
  ⟨AdrSet.not_mem_union hp_atd hc.atd, hc.ca, hc.code⟩

lemma Devm.pop_err_snd {d : Devm} {x : EvmError × Devm}
    (h : Devm.pop d = .error x) : x.2 = d := by
  simp only [Devm.pop_def] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp)

lemma Devm.popToAdr_err_snd {d : Devm} {x : EvmError × Devm}
    (h : Devm.popToAdr d = .error x) : x.2 = d := by
  rw [Devm.popToAdr_def] at h
  rcases hp : d.pop with e | ⟨v, d0⟩
  · rw [hp] at h; injection h with h; rw [← h]; exact Devm.pop_err_snd hp
  · rw [hp] at h; exact absurd h (by simp)

lemma chargeGas_err_snd {cost : Nat} {d : Devm} {x : EvmError × Devm}
    (h : chargeGas cost d = .error x) : x.2 = d := by
  simp only [chargeGas_def] at h
  split at h
  · injection h with h; exact (congrArg Prod.snd h).symm
  · exact absurd h (by simp)

lemma Except.assert_err_snd {p : Prop} [Decidable p] {d : Devm} {s : EvmError}
    {x : EvmError × Devm} (h : Except.assert p (⟨s, d⟩ : EvmError × Devm) = .error x) :
    x.2 = d := by
  simp only [Except.assert] at h
  split at h
  · exact absurd h (by simp)
  · injection h with h; exact (congrArg Prod.snd h).symm

lemma Devm.NoDel.pop {wa : Adr} {d d' : Devm} {v : B256}
    (hd : Devm.NoDel wa d) (h : Devm.pop d = .ok ⟨v, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.pop_delSets_eq h).symm (Devm.pop_getCode h).symm

lemma Devm.NoDel.popToNat {wa : Adr} {d d' : Devm} {n : Nat}
    (hd : Devm.NoDel wa d) (h : Devm.popToNat d = .ok ⟨n, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.popToNat_delSets_eq h).symm (Devm.popToNat_getCode h).symm

lemma Devm.NoDel.popToAdr {wa : Adr} {d d' : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) (h : Devm.popToAdr d = .ok ⟨a, d'⟩) : Devm.NoDel wa d' :=
  hd.of_eqs (Devm.popToAdr_delSets_eq h).symm (Devm.popToAdr_getCode h).symm

lemma Devm.NoDel.chargeGas {wa : Adr} {d d' : Devm} {cost : Nat}
    (hd : Devm.NoDel wa d) (h : chargeGas cost d = .ok d') : Devm.NoDel wa d' :=
  hd.of_eqs (chargeGas_delSets_eq h).symm (chargeGas_getCode h).symm

lemma Devm.NoDel.memExtends {wa : Adr} {d : Devm} {ranges : List (Nat × Nat)}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (d.memExtends ranges) := by
  refine hd.of_eqs ?_ Devm.memExtends_getCode.symm
  rfl

lemma Devm.NoDel.addAccessedAddress {wa : Adr} {d : Devm} {a : Adr}
    (hd : Devm.NoDel wa d) : Devm.NoDel wa (Jaune.addAccessedAddress d a) := by
  refine hd.of_eqs ?_ addAccessedAddress_getCode.symm
  rfl

def Benv.EquivForDelegation (b1 b2 : Benv) : Prop :=
  b2.createdAccounts = b1.createdAccounts ∧
  ∀ a, (b1.state.getCode a).toList ≠ [] →
    ¬ isValidDelegation (b1.state.getCode a) →
    b2.state.getCode a = b1.state.getCode a

lemma Benv.EquivForDelegation_refl (b : Benv) : Benv.EquivForDelegation b b := by
  refine ⟨rfl, fun _ _ _ => rfl⟩

lemma Benv.EquivForDelegation_trans {b1 b2 b3 : Benv} (h12 : Benv.EquivForDelegation b1 b2) (h23 : Benv.EquivForDelegation b2 b3) :
    Benv.EquivForDelegation b1 b3 := by
  rcases h12 with ⟨h1c, h1code⟩
  rcases h23 with ⟨h2c, h2code⟩
  refine ⟨by rw [h2c, h1c], fun a ha hnd => ?_⟩
  have h1 := h1code a ha hnd
  have ha2' : (b2.state.getCode a).toList ≠ [] := by
    rw [h1]
    exact ha
  have hnd2 : ¬ isValidDelegation (b2.state.getCode a) := by
    rw [h1]
    exact hnd
  rw [h2code a ha2' hnd2, h1]

lemma bind_eq_ok_Except {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {res : β} :
    bind x f = Except.ok res → ∃ a, x = Except.ok a ∧ f a = Except.ok res := by
  intro h
  cases x with
  | error e =>
    dsimp [bind, Except.bind] at h
    contradiction
  | ok a =>
    dsimp [bind, Except.bind] at h
    exact ⟨a, rfl, h⟩

lemma Msg.NoDel.benvAfterTransfer {wa : Adr} {msg : Msg} {benv : Benv}
    (h_run : msg.benvAfterTransfer = .ok benv)
    (h : Msg.NoDel wa msg) : Msg.NoDel wa (msg.withBenv benv) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h_run
    rw [h_stv] at h_run
    simp only [if_true] at h_run
    unfold Benv.subBal at h_run
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h_run
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h_run
      contradiction
    · rw [h_sub] at h_run
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h_run
      injection h_run with hB
      have hBc : benv.createdAccounts = msg.benv.createdAccounts := by
        rw [← hB]; rfl
      have h_code_add : benv.state.getCode wa = st_mid.getCode wa := by
        have hBs : benv.state = st_mid.addBal msg.currentTarget msg.value := by
          rw [← hB]; rfl
        rw [hBs]; exact State.addBal_getCode st_mid msg.currentTarget wa msg.value
      have h_code_sub : st_mid.getCode wa = msg.benv.state.getCode wa := by
        exact State.subBal_getCode h_sub
      have h_code : ((msg.withBenv benv).benv.state.getCode wa).toList ≠ [] := by
        change (benv.state.getCode wa).toList ≠ []
        rw [h_code_add, h_code_sub]
        exact h.code
      exact ⟨hBc ▸ h.ca, h_code⟩
  · unfold Msg.benvAfterTransfer at h_run
    rw [if_neg h_stv] at h_run
    have heq : benv = msg.benv := (Except.ok.inj h_run).symm
    subst heq
    exact h

/-! ## 4. Balance-sum relations and primitive state updates -/

def State.balSum (st : Jaune.State) : Nat :=
  sum st.bal

def Devm.balSum (d : Devm) : Nat :=
  State.balSum d.state

def State.BalNoninc (pre post : Jaune.State) : Prop :=
  State.balSum post ≤ State.balSum pre

def Devm.BalNoninc (pre post : Devm) : Prop :=
  Devm.balSum post ≤ Devm.balSum pre

def State.BalGrowth (allowance : Nat) (pre post : Jaune.State) : Prop :=
  State.balSum post ≤ State.balSum pre + allowance

def State.SumNof (st : Jaune.State) : Prop :=
  State.balSum st < 2 ^ 256

def Devm.SumNof (d : Devm) : Prop :=
  Devm.balSum d < 2 ^ 256

lemma balNoninc_refl_trans :
    (ReflexiveRel State.BalNoninc ∧ TransitiveRel State.BalNoninc) ∧
    (ReflexiveRel Devm.BalNoninc ∧ TransitiveRel Devm.BalNoninc) := by
  exact ⟨⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩,
         ⟨fun _ => Nat.le_refl _, fun _ _ _ h1 h2 => Nat.le_trans h2 h1⟩⟩

lemma adr_toNat_lt_size_local (a : Adr) : a.toNat < 2 ^ 160 := by
  rw [← toAdr_toNat a, Nat.toNat_toAdr, Nat.lo]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

lemma sumBelow_setBal_eq_local (st : Jaune.State) (a : Adr) (v : B256)
    (n : Nat) (hn : n ≤ a.toNat) (hsize : n ≤ 2 ^ 160) :
    sumBelow (fun x => (st.setBal a v).bal x) n =
      sumBelow (fun x => st.bal x) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    rw [ih (Nat.le_of_succ_le hn) (Nat.le_of_succ_le hsize)]
    have hnlt : n < a.toNat := Nat.lt_of_succ_le hn
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    have hne : n.toAdr ≠ a := by
      intro heq
      have hnat := congrArg Adr.toNat heq
      rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
      omega
    have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
      State.get_set_ne hne.symm
    have hbal : (st.setBal a v).bal n.toAdr = st.bal n.toAdr := by
      dsimp [State.bal, State.setBal]
      have hget' : (st.set a ((st.get a).withBal v)).get n.toAdr =
          st.get n.toAdr := by
        simpa [State.setBal] using hget
      rw [hget']
    rw [hbal]

lemma sumBelow_setBal_add_local (st : Jaune.State) (a : Adr) (v : B256)
    (n : Nat) (hsize : n ≤ 2 ^ 160) (ha : a.toNat < n) :
    sumBelow (fun x => (st.setBal a v).bal x) n + (st.bal a).toNat =
      sumBelow (fun x => st.bal x) n + v.toNat := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumBelow_succ, sumBelow_succ]
    have hnsize : n < 2 ^ 160 := Nat.lt_of_succ_le hsize
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha_lt | ha_eq
    · have hih := ih (Nat.le_of_succ_le hsize) ha_lt
      have hne : n.toAdr ≠ a := by
        intro heq
        have hnat := congrArg Adr.toNat heq
        rw [Nat.toNat_toAdr, Nat.lo_eq_of_lt hnsize] at hnat
        omega
      have hget : (st.setBal a v).get n.toAdr = st.get n.toAdr :=
        State.get_set_ne hne.symm
      change sumBelow (fun x => (st.setBal a v).bal x) n +
          ((st.setBal a v).get n.toAdr).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get n.toAdr).bal.toNat + v.toNat
      rw [hget]
      omega
    · have hprefix := sumBelow_setBal_eq_local st a v n
        (Nat.le_of_eq ha_eq.symm) (Nat.le_of_succ_le hsize)
      have haddr : n.toAdr = a := by
        rw [← ha_eq]
        exact toAdr_toNat a
      rw [hprefix, haddr]
      change sumBelow (fun x => st.bal x) n +
          ((st.setBal a v).get a).bal.toNat + (st.bal a).toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      dsimp [State.setBal]
      rw [State.get_set_self]
      change sumBelow (fun x => st.bal x) n + v.toNat +
          (st.get a).bal.toNat =
        sumBelow (fun x => st.bal x) n + (st.get a).bal.toNat + v.toNat
      omega

lemma State.balSum_setBal (st : Jaune.State) (a : Adr) (v : B256) :
    State.balSum (st.setBal a v) + (st.bal a).toNat =
      State.balSum st + v.toNat := by
  have hmax : Adr.max.toNat.succ = 2 ^ 160 := by decide
  have ha : a.toNat < Adr.max.toNat.succ := by
    rw [hmax]
    exact adr_toNat_lt_size_local a
  simpa [State.balSum, sum] using
    (sumBelow_setBal_add_local st a v Adr.max.toNat.succ
      (by rw [hmax]) ha)

lemma State.balSum_subBal {st mid : Jaune.State} {a : Adr} {v : B256}
    (h : st.subBal a v = some mid) :
    State.balSum mid + v.toNat = State.balSum st := by
  unfold State.subBal at h
  split at h
  · contradiction
  · injection h with h_mid
    subst h_mid
    have h_set := State.balSum_setBal st a (st.bal a - v)
    rename_i h_not_lt
    have h_le : v ≤ st.bal a := le_of_not_gt h_not_lt
    have h_le2 : v.toNat ≤ (st.bal a).toNat := B256.toNat_le_toNat h_le
    rw [B256.toNat_sub_eq_of_le _ _ h_le] at h_set
    omega

lemma State.addBal_growth (st : Jaune.State) (a : Adr) (v : B256) :
    State.BalGrowth v.toNat st (st.addBal a v) := by
  unfold State.addBal State.BalGrowth
  have h := State.balSum_setBal st a (st.bal a + v)
  rw [B256.toNat_add] at h
  unfold Nat.lo at h
  have h_mod := Nat.mod_le ((st.bal a).toNat + v.toNat) (2^256)
  omega

/- This lemma is the reusable conservation/nonincrease theorem for value transfer,
   including the recipient-overflow case.  -/
lemma State.sub_addBal_noninc {st mid : Jaune.State}
    {src dst : Adr} {v : B256}
    (hsub : st.subBal src v = some mid) :
    State.BalNoninc st (mid.addBal dst v) := by
  dsimp [State.BalNoninc]
  have h1 := State.addBal_growth mid dst v
  dsimp [State.BalGrowth] at h1
  have h2 := State.balSum_subBal hsub
  omega

lemma State.setBal_zero_noninc (st : Jaune.State) (a : Adr) :
    State.BalNoninc st (st.setBal a 0) := by
  unfold State.BalNoninc
  have h := State.balSum_setBal st a 0
  have hz : ((0 : B256).toNat) = 0 := by decide
  rw [hz, Nat.add_zero] at h
  omega

lemma Devm.balNoninc_of_state {pre post : Devm}
    (h : State.BalNoninc pre.state post.state) : Devm.BalNoninc pre post := by
  exact h

lemma Devm.balNoninc_of_getBal_eq {pre post : Devm}
    (h : post.getBal = pre.getBal) : Devm.BalNoninc pre post := by
  unfold Devm.BalNoninc Devm.balSum State.balSum
  change sum post.getBal ≤ sum pre.getBal
  rw [h]

/-! ## 5. Balance effects of instruction and message semantic units -/

def MessageExecution := Except (EvmError × Jaune.State × AdrSet × Tra) Devm

def MessageExecution.state : MessageExecution → Jaune.State
  | .ok d => d.state
  | .error ⟨_, st, _, _⟩ => st

def MessageExecution.Rel
    (R : Jaune.State → Jaune.State → Prop)
    (pre : Jaune.State) (out : MessageExecution) : Prop :=
  R pre out.state

def BenvExecution.state : Except (EvmError × Jaune.State × AdrSet × Tra) Benv →
    Jaune.State
  | .ok benv => benv.state
  | .error ⟨_, st, _, _⟩ => st

/-! Error-side `getBal` frame lemmas, mirroring the generated `*_getCode_err`
family in `Blanc/Common.lean`: every regular-instruction error path leaves
balances unchanged. -/

lemma Rinst.inv_getBal_err
    {pc sevm devm r err}
    (run : Rinst.run ⟨pc, sevm, devm⟩ r = Except.error err) (a : Adr) :
    err.2.getBal a = devm.getBal a := by
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc devm sevm; rw [run] at hf
    exact (Devm.StateWriteFrame.getBal_eq hf a).symm
  rcases eq_or_ne r .tstore with rfl | ht
  · have hf := Rinst.tstore_run_transientWriteFrame pc devm sevm; rw [run] at hf
    exact congrFun (congrArg (fun s => s.bal) hf.state).symm a
  · have hf := Rinst.run_instructionFrame pc sevm devm r hs ht; rw [run] at hf; exact (hf.getBal a).symm

lemma Rinst.balance_effect (r : Rinst) :
    Rinst.Effect Devm.BalNoninc r := by
  intro pc sevm pre out hrun
  cases out with
  | ok post => exact Devm.balNoninc_of_getBal_eq (Rinst.preserves_bal hrun).symm
  | error err => exact Devm.balNoninc_of_getBal_eq (funext fun a => Rinst.inv_getBal_err hrun a)

lemma Jinst.balance_effect (j : Jinst) :
    Jinst.Effect Devm.BalNoninc j := by
  intro evm out hrun
  have hf := Jinst.run_instructionFrame evm j
  rw [hrun] at hf
  cases out <;> exact Devm.balNoninc_of_getBal_eq
    (funext fun a => (hf.getBal a).symm)

lemma Ninst.push_balance_effectRec {xs : Bytes} {hxs : xs.length ≤ 32} :
    Ninst.EffectRec Devm.BalNoninc (.push xs hxs) := by
  exact Ninst.push_effectRec_of_instructionFrame (R := Devm.BalNoninc)
    (fun _ _ hf =>
      Devm.balNoninc_of_getBal_eq (funext fun a => (hf.getBal a).symm))

lemma Linst.dest_balance_effect :
    Linst.Effect Devm.BalNoninc .dest := by
  intro sevm pre out run
  dsimp [Linst.Run, Linst.run] at run
  revert run
  dsimp [bind, Except.bind]
  cases h1 : pre.popToAdr <;> dsimp
  case error err =>
    intro run
    rw [← run]
    apply Devm.balNoninc_of_getBal_eq
    rw [Devm.popToAdr_err_snd h1]
  case ok res1 =>
    have hpop : res1.2.getBal = pre.getBal := by
      funext a
      exact Devm.popToAdr_getBal_eq h1 a
    have hacc :
        (if res1.1 ∉ res1.2.accessedAddresses then
            (addAccessedAddress res1.2 res1.1, gasSelfDestruct + gasColdAccountAccess)
          else (res1.2, gasSelfDestruct)).1.getBal = res1.2.getBal := by
      funext a
      split <;> rfl
    cases h2 : chargeGas
        (if ((if res1.1 ∉ res1.2.accessedAddresses then
                    (addAccessedAddress res1.2 res1.1,
                      gasSelfDestruct + gasColdAccountAccess)
                  else (res1.2, gasSelfDestruct)).1.getAcct res1.1).Empty ∧
              ¬(res1.2.getAcct sevm.currentTarget).bal = 0 then
          (if res1.1 ∉ res1.2.accessedAddresses then
                (addAccessedAddress res1.2 res1.1,
                  gasSelfDestruct + gasColdAccountAccess)
              else (res1.2, gasSelfDestruct)).2 + gasSelfDestructNewAccount
        else
          (if res1.1 ∉ res1.2.accessedAddresses then
              (addAccessedAddress res1.2 res1.1,
                gasSelfDestruct + gasColdAccountAccess)
            else (res1.2, gasSelfDestruct)).2)
        (if res1.1 ∉ res1.2.accessedAddresses then
            (addAccessedAddress res1.2 res1.1,
              gasSelfDestruct + gasColdAccountAccess)
          else (res1.2, gasSelfDestruct)).1 <;> dsimp
    case error err =>
      intro run
      rw [← run]
      apply Devm.balNoninc_of_getBal_eq
      rw [chargeGas_err_snd h2]
      exact hacc.trans hpop
    case ok res2 =>
      have hpre : res2.getBal = pre.getBal := by
        funext a
        exact (chargeGas_getBal_eq h2 a).trans
          (congrFun (hacc.trans hpop) a)
      cases h3 : assertDynamic sevm res2
      case error err =>
        intro run
        rw [← run]
        apply Devm.balNoninc_of_getBal_eq
        have herr : err.2 = res2 := by
          dsimp [assertDynamic] at h3
          exact Except.assert_err_snd h3
        rw [herr]
        exact hpre
      case ok _ =>
        cases h4 : res2.subBal sevm.currentTarget
            (res1.2.getAcct sevm.currentTarget).bal <;> dsimp [Option.toExcept]
        case none =>
          intro run
          rw [← run]
          exact Devm.balNoninc_of_getBal_eq hpre
        case some res3 =>
          have hsub : res2.state.subBal sevm.currentTarget
              (res1.2.getAcct sevm.currentTarget).bal = some res3.state := by
            dsimp [Devm.subBal, Option.bind] at h4
            cases hs : res2.state.subBal sevm.currentTarget
                (res1.2.getAcct sevm.currentTarget).bal
            · rw [hs] at h4
              contradiction
            · rw [hs] at h4
              injection h4 with heq
              subst heq
              rfl
          have htransfer : State.BalNoninc pre.state
              (res3.addBal res1.1
                (res1.2.getAcct sevm.currentTarget).bal).state := by
            have ht := State.sub_addBal_noninc (dst := res1.1) hsub
            have hbal : res2.state.bal = pre.state.bal := hpre
            unfold State.BalNoninc State.balSum at ht ⊢
            rw [hbal] at ht
            exact ht
          by_cases hdel : sevm.currentTarget ∈
              (res3.addBal res1.1
                (res1.2.getAcct sevm.currentTarget).bal).createdAccounts
          · simp only [hdel, if_pos]
            intro run
            rw [← run]
            unfold Execution.Rel Outcome.Rel
            apply Devm.balNoninc_of_state
            apply balNoninc_refl_trans.1.2 htransfer
            exact State.setBal_zero_noninc _ _
          · simp only [hdel]
            intro run
            rw [← run]
            unfold Execution.Rel Outcome.Rel
            exact Devm.balNoninc_of_state htransfer

lemma Linst.balance_effect (l : Linst) :
    Linst.Effect Devm.BalNoninc l := by
  rcases eq_or_ne l .dest with rfl | h_not_dest
  · exact Linst.dest_balance_effect
  · intro sevm pre out run
    have hf := Linst.run_instructionFrame sevm pre l h_not_dest
    rw [run] at hf
    cases out <;> exact Devm.balNoninc_of_getBal_eq
      (funext fun a => (hf.getBal a).symm)

/-- An instruction frame is balance-silent, hence transports directly to the
total-balance preorder used by the balance-effect layer. -/
lemma Devm.instructionFrame_refines_balNoninc :
    ∀ ⦃d d'⦄, Devm.InstructionFrame d d' → Devm.BalNoninc d d' := by
  intro pre post h
  apply Devm.balNoninc_of_state
  rw [h.state]
  exact balNoninc_refl_trans.1.1 _

lemma Msg.benvAfterTransfer_balance_effect {msg : Msg}
    {out : Except (EvmError × Jaune.State × AdrSet × Tra) Benv}
    (h : msg.benvAfterTransfer = out) :
    State.BalNoninc msg.benv.state (BenvExecution.state out) := by
  by_cases h_stv : msg.shouldTransferValue = true
  · unfold Msg.benvAfterTransfer at h
    rw [h_stv] at h
    simp only [if_true] at h
    unfold Benv.subBal at h
    rcases h_sub : msg.benv.state.subBal msg.caller msg.value with _ | st_mid
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      exact Nat.le_refl _
    · rw [h_sub] at h
      simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
      rw [← h]
      change State.BalNoninc msg.benv.state (st_mid.addBal msg.currentTarget msg.value)
      exact State.sub_addBal_noninc h_sub
  · unfold Msg.benvAfterTransfer at h
    rw [if_neg h_stv] at h
    rw [← h]
    exact Nat.le_refl _

lemma processCreateMessage.chargeCodeGas_balance_effect
    {rules : ForkRules} {pre : Devm} {out : Execution}
    (h : processCreateMessage.chargeCodeGas rules pre = out) :
    Execution.Rel Devm.BalNoninc pre out := by
  rcases out with ⟨err, d⟩ | d <;> simp only [Execution.Rel, Outcome.Rel]
  · simp only [processCreateMessage.chargeCodeGas] at h
    split at h
    · simp only [Except.error.injEq] at h
      cases h
      exact balNoninc_refl_trans.2.1 pre
    · dsimp [Bind.bind, Except.bind] at h
      split at h
      · rename_i code neq ex errCharge hCharge
        simp only [Except.error.injEq] at h
        cases h
        have hstate := chargeGas_err_snd hCharge
        change d = pre at hstate
        rw [hstate]
        exact balNoninc_refl_trans.2.1 pre
      · split at h
        · simp only [Except.error.injEq] at h
          cases h
          rename_i code neq ex hSize hCharge
          have hb := Devm.burn_of_chargeGas hCharge
          apply Devm.balNoninc_of_state
          rw [hb.state]
          exact balNoninc_refl_trans.1.1 d.state
        · cases h
  · simp only [id]
    simp only [processCreateMessage.chargeCodeGas] at h
    split at h
    · cases h
    · dsimp [Bind.bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i code neq ex hSize hCharge
          simp only [Except.ok.injEq] at h
          cases h
          have hb := Devm.burn_of_chargeGas hSize
          apply Devm.balNoninc_of_state
          rw [hb.state]
          exact balNoninc_refl_trans.1.1 d.state

lemma executePrecomp_balance_effect {evm : Evm} {a : Adr} {out : Execution}
    (h : executePrecomp evm a = out) :
    Execution.Rel Devm.BalNoninc evm.dyna out := by
  subst out
  unfold executePrecomp applyPrecompResult Execution.Rel Outcome.Rel
    Devm.BalNoninc Devm.balSum State.balSum
  cases precompileRun evm a <;> rfl

/-- `executeCode.handleError` selects between the raw execution result and a
rolled-back state without introducing any balance write of its own, so it
transports a raw `Devm.BalNoninc` frame to a `State.BalNoninc` on the handled
message outcome. -/
lemma executeCode.handleError_balance_effect {pre : Devm} {raw : Execution}
    {handled : MessageExecution}
    (hb : Execution.Rel Devm.BalNoninc pre raw)
    (hh : executeCode.handleError raw = handled) :
    State.BalNoninc pre.state (MessageExecution.state handled) := by
  rcases raw with ⟨err, d⟩ | d
  · cases err <;>
      (simp only [executeCode.handleError] at hh; subst handled; exact hb)
  · simp only [executeCode.handleError] at hh
    subst handled
    exact hb

/-- Frame projections of the two child messages, as explicit equations: the
defeq is cheap to state and expensive to re-derive at every use site. -/
lemma callMsg_benv_state
    {sevm : Sevm} {evm1 : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {calldata : Bytes}
    {code : ByteArray} {dp : Bool} :
    ( callMsg sevm evm1 gas value caller target codeAddress stv isSt calldata
        code dp ).benv.state = evm1.state := rfl

lemma createMsg_benv_state
    {sevm : Sevm} {devm : Devm} {createGas : Nat} {endowment : B256}
    {newAddress : Adr} {calldata : Bytes} :
    (createMsg sevm devm createGas endowment newAddress calldata).benv.state
      = devm.state := rfl

/-- The create driver is the call driver on the seeded message, followed by the
create-specific settlement. -/
lemma processCreateMessage_eq (msg : Msg) :
    processCreateMessage msg =
      processCreateMessage.settle msg
        (processMessage (processCreateMessage.msg msg)) := by
  unfold processCreateMessage processMessage runFrame Frame.enter Frame.settle
    Frame.settleMsg Frame.ofCreate Frame.ofCall
  rcases (processCreateMessage.msg msg).benvAfterTransfer with e | benv <;>
    simp only [reduceIte]
  · rfl
  · rcases executeCode.enter ((processCreateMessage.msg msg).withBenv benv) with
      evm | raw
    · rfl
    · rfl

lemma processCreateMessage.settle_error {msg : Msg}
    {e : EvmError × Jaune.State × AdrSet × Tra} :
    processCreateMessage.settle msg (.error e) = .error e := rfl

/-- A failed child message aborts the CREATE-family return path. -/
lemma Resume.create_run_error {parent : Devm} {newAddress : Adr}
    {e : EvmError × Jaune.State × AdrSet × Tra} {sf : Devm}
    (h : (Resume.create parent newAddress).run (.error e) = .ok sf) : False := by
  rcases e with ⟨err, st, ac, tra⟩
  unfold Resume.run liftToExecution at h
  cases h

lemma processMessage.settle_error {msg : Msg}
    {e : EvmError × Jaune.State × AdrSet × Tra} :
    processMessage.settle msg (.error e) = .error e := rfl

/-- Master balance effect for the code-execution layer: running the callee's
code (interpreter, precompile, or the empty-code no-op) never increases the
total balance relative to the freshly-initialised message state. The `Xlot`
witness carries the interpreter's own `Devm.BalNoninc` frame; the precompile
branch supplies its frame directly. -/
lemma ExecuteCode.balance_effect {msg : Msg} {xl : Xlot}
    {ex : Except (EvmError × Jaune.State × AdrSet × Tra) Devm}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (hec : ExecuteCode msg xl ex) :
    State.BalNoninc (initEvm msg).dyna.state (MessageExecution.state ex) := by
  unfold ExecuteCode at hec
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at hec
  · rcases hec with ⟨raw, hxl_eq, hh⟩
    rw [hxl_eq] at hxl
    rw [executeCode.enter_inl henter] at hxl
    exact executeCode.handleError_balance_effect hxl hh.symm
  · obtain ⟨adr, hraw⟩ := executeCode.enter_inr henter
    refine executeCode.handleError_balance_effect ?_ hec.2.symm
    rw [hraw]
    exact executePrecomp_balance_effect rfl

lemma ProcessMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp run
  unfold FrameBody at hbody
  rcases h_benv : msg.benvAfterTransfer with ⟨err, st, ac, tra⟩ | benv <;>
    rw [h_benv] at hbody
  · rw [hbody.2, processMessage.settle_error]
    have ht := Msg.benvAfterTransfer_balance_effect h_benv
    simp only [MessageExecution.Rel, MessageExecution.state,
      BenvExecution.state] at ht ⊢
    exact ht
  · have htransfer := Msg.benvAfterTransfer_balance_effect h_benv
    have hexec : State.BalNoninc benv.state (MessageExecution.state r0) := by
      have h := ExecuteCode.balance_effect hxl hbody
      have hinit : (initEvm (msg.withBenv benv)).dyna.state = benv.state := rfl
      rwa [hinit] at h
    unfold processMessage.settle
    rcases r0 with e' | evm
    · exact Nat.le_trans hexec htransfer
    · dsimp only [bind, Except.bind]
      split
      · exact balNoninc_refl_trans.1.1 _
      · exact Nat.le_trans hexec htransfer

lemma ProcessCreateMessage.balance_effect {msg : Msg} {xl : Xlot}
    {out : MessageExecution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : ProcessCreateMessage msg xl out) :
    MessageExecution.Rel State.BalNoninc msg.benv.state out := by
  obtain ⟨ex', run_pm, rfl⟩ := ProcessCreateMessage.iff_processMessage.mp run
  have h_seed : (processCreateMessage.msg msg).benv.state.bal = msg.benv.state.bal := by
    change ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
      msg.currentTarget).bal = msg.benv.state.bal
    rw [State.incrNonce_bal, State.setStor_bal]
  have h_pm := ProcessMessage.balance_effect hxl run_pm
  unfold MessageExecution.Rel State.BalNoninc State.balSum at h_pm
  rw [h_seed] at h_pm
  unfold processCreateMessage.settle
  rcases ex' with e' | evm
  · exact h_pm
  · dsimp only [bind, Except.bind]
    split
    · cases h_cg : processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
      | error err =>
        rcases err with ⟨err_msg, err_evm⟩
        have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
        unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum
          State.balSum at h_charge
        dsimp only [id] at h_charge
        dsimp only [MessageExecution.state] at h_pm
        cases err_msg
        case halt => exact balNoninc_refl_trans.1.1 _
        all_goals exact Nat.le_trans h_charge h_pm
      | ok devm_charge =>
        dsimp only []
        have h_charge := processCreateMessage.chargeCodeGas_balance_effect h_cg
        unfold Execution.Rel Outcome.Rel Devm.BalNoninc Devm.balSum
          State.balSum at h_charge
        dsimp only [id] at h_charge
        dsimp only [MessageExecution.state] at h_pm
        change sum (devm_charge.state.setCode msg.currentTarget
          ⟨⟨devm_charge.output⟩⟩).bal ≤ sum msg.benv.state.bal
        rw [State.setCode_bal]
        exact Nat.le_trans h_charge h_pm
    · exact balNoninc_refl_trans.1.1 _

/-- The create prefix's sender nonce bump is a non-balance world write. -/
lemma Devm.incrNonce_balance_effect (pre : Devm) (a : Adr) :
    Devm.BalNoninc pre (pre.incrNonce a) := by
  unfold Devm.BalNoninc Devm.balSum State.balSum
  change sum (pre.state.incrNonce a).bal ≤ sum pre.state.bal
  rw [State.incrNonce_bal]

/-- Child-error incorporation installs the child's already-accounted world;
the parent fields it retains do not include balances. -/
lemma incorporateChildOnError_balance_effect
    {pre parent child : Devm} {returnData : Bytes}
    (h : State.BalNoninc pre.state child.state) :
    Devm.BalNoninc pre
      (incorporateChildOnError parent child returnData) := by
  apply Devm.balNoninc_of_state
  dsimp only [incorporateChildOnError]
  exact h

/-- Child-success incorporation has the same precise balance projection as
the error form, while differing in the non-balance fields it incorporates. -/
lemma incorporateChildOnSuccess_balance_effect
    {pre parent child : Devm} {returnData : Bytes}
    (h : State.BalNoninc pre.state child.state) :
    Devm.BalNoninc pre
      (incorporateChildOnSuccess parent child returnData) := by
  apply Devm.balNoninc_of_state
  dsimp only [incorporateChildOnSuccess]
  exact h

/-- Pushing a status word and writing the returned output to memory are both
frame moves, so they carry a balance bound on the incorporated machine. -/
lemma Devm.pushMemWrite_balance {pre d : Devm} {v : B256} {oi : Nat} {o : Bytes}
    (h : Devm.BalNoninc pre d) :
    Execution.Rel Devm.BalNoninc pre
      (d.push v >>= fun d' => .ok (d'.memWrite oi o)) := by
  refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 h ?_
  refine Execution.Rel.bind balNoninc_refl_trans.2.2
    (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
      (Devm.push_instructionFrame v d)) ?_
  intro d'
  exact Devm.instructionFrame_refines_balNoninc
    (Devm.memWrite_instructionFrame d' oi o)

/-- A status push onto a machine already bounded against `pre` keeps the
bound, on both outcomes. -/
lemma Devm.push_balance_gen {v : B256} {pre d : Devm} {ex : Execution}
    (h : Devm.push v d = ex) (hf : Devm.BalNoninc pre d) :
    Execution.Rel Devm.BalNoninc pre ex := by
  subst h
  exact Execution.Rel.trans_left balNoninc_refl_trans.2.2 hf
    (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
      (Devm.push_instructionFrame v d))

/-- The CREATE-family return path never raises the parent's balance sum: the
child's world is already bounded and the status push is a frame move. -/
lemma Resume.create_balance {parent : Devm} {newAddress : Adr}
    {r : MessageExecution}
    (h : State.BalNoninc parent.state (MessageExecution.state r)) :
    Execution.Rel Devm.BalNoninc parent
      ((Resume.create parent newAddress).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;> dsimp only [bind, Except.bind]
  · simp only [Execution.Rel, Outcome.Rel]
    exact h
  · split
    · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
        (incorporateChildOnError_balance_effect h)
        (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
          (Devm.push_instructionFrame 0 _))
    · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
        (incorporateChildOnSuccess_balance_effect h)
        (Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc
          (Devm.push_instructionFrame _ _))

/-- The CALL-family return path, likewise: incorporation plus a push and a
memory write. -/
lemma Resume.call_balance {parent : Devm} {oi os : Nat} {r : MessageExecution}
    (h : State.BalNoninc parent.state (MessageExecution.state r)) :
    Execution.Rel Devm.BalNoninc parent ((Resume.call parent oi os).run r) := by
  unfold Resume.run liftToExecution
  rcases r with ⟨err, state, ac, tra⟩ | child <;> dsimp only [bind, Except.bind]
  · simp only [Execution.Rel, Outcome.Rel]
    exact h
  · split
    · exact Devm.pushMemWrite_balance (incorporateChildOnError_balance_effect h)
    · exact Devm.pushMemWrite_balance (incorporateChildOnSuccess_balance_effect h)

/-- Canonical balance-effect master for generic calls.  The call prefix is
balance-silent; all balance changes are delegated to `ProcessMessage`, and
child incorporation merely installs the child's already-bounded state. -/
lemma GenericCall.balanceEffect
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code dp xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  have hret : Devm.BalNoninc pre (pre.withReturnData []) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  -- depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 hret ?_
    refine Resume.call_balance ?_
    have h := ProcessMessage.balance_effect hxl hframe
    unfold MessageExecution.Rel at h
    rwa [callMsg_benv_state] at h

lemma GenericCall.balance_effect
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code dp xl out) :
    Execution.Rel Devm.BalNoninc pre out :=
  GenericCall.balanceEffect hxl run

/-- Canonical balance-effect master for generic creates.  Unlike calls, its
prefix contains the sender nonce write and its child path performs fresh
account initialisation before installing the child world. -/
lemma GenericCreate.balanceEffect
    {sevm : Sevm} {pre : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCreate sevm pre endowment newAddress mi ms xl out) :
    Execution.Rel Devm.BalNoninc pre out := by
  have hgas : Devm.BalNoninc pre
      (pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)) :=
    Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  have hret : Devm.BalNoninc pre
      ((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData []) :=
    balNoninc_refl_trans.2.2 hgas
      (Devm.instructionFrame_refines_balNoninc
        (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl))
  have hnonce : Devm.BalNoninc pre
      (addAccessedAddress
        (((pre.withGasLeft (pre.gasLeft - except64th pre.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress) := by
    refine balNoninc_refl_trans.2.2 hret ?_
    refine balNoninc_refl_trans.2.2
      (Devm.incrNonce_balance_effect _ sevm.currentTarget) ?_
    exact Devm.instructionFrame_refines_balNoninc
      (addAccessedAddress_instructionFrame _ newAddress)
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  -- init-code-size assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    exact balNoninc_refl_trans.2.1 _
  -- static-context assertion failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    split at heq <;> cases heq
    exact hgas
  -- balance / max-nonce / depth-zero early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  -- balance / max-nonce / depth-zero early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    refine Devm.push_balance_gen heq (balNoninc_refl_trans.2.2 hret ?_)
    exact Devm.instructionFrame_refines_balNoninc
      (Devm.instructionFrame_of_world_eq rfl rfl rfl rfl)
  -- address-collision early exit, push failed
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    exact Devm.push_balance_gen heq hnonce
  -- address-collision early exit, push succeeded
  · obtain ⟨-, rfl⟩ := run
    rename_i heq
    exact Devm.push_balance_gen heq hnonce
  -- the child frame is entered
  · obtain ⟨r, hframe, rfl⟩ := run
    refine Execution.Rel.trans_left balNoninc_refl_trans.2.2 hnonce ?_
    refine Resume.create_balance ?_
    have h := ProcessCreateMessage.balance_effect hxl hframe
    unfold MessageExecution.Rel at h
    rwa [createMsg_benv_state] at h

lemma GenericCreate.balance_effect
    {sevm : Sevm} {pre : Devm} {endowment : B256} {newAddress : Adr}
    {mi ms : Nat} {xl : Xlot} {out : Execution}
    (hxl : Xlot.Rel Devm.BalNoninc xl)
    (run : GenericCreate sevm pre endowment newAddress mi ms xl out) :
    Execution.Rel Devm.BalNoninc pre out :=
  GenericCreate.balanceEffect hxl run

lemma Xinst.balance_effectRec (x : Xinst) :
    Xinst.EffectRec Devm.BalNoninc x := by
  intro sevm pre xl out hxl run
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm pre x with ⟨ex, hs, hframe⟩ |
    ⟨d, e, na, mi, ms, hf, hs⟩ |
    ⟨d, d₀, g, v, c, t, cadr, stv, isSt, ii, isz, oi, osz, code, dp,
      hf, -, -, -, hs⟩ <;> rw [hs] at run
  -- the whole step stayed inside the instruction frame
  · obtain ⟨-, rfl⟩ := run
    exact Outcome.Rel.mono Devm.instructionFrame_refines_balNoninc hframe
  -- dispatched to the CREATE family
  · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (Devm.instructionFrame_refines_balNoninc hf)
      (GenericCreate.balanceEffect hxl run)
  -- dispatched to the CALL family
  · exact Execution.Rel.trans_left balNoninc_refl_trans.2.2
      (Devm.instructionFrame_refines_balNoninc hf)
      (GenericCall.balanceEffect hxl run)

lemma Ninst.balance_effectRec (n : Ninst) :
    Ninst.EffectRec Devm.BalNoninc n := by
  cases n
  case reg r =>
    apply Ninst.effectRec_reg
    apply Rinst.balance_effect
  case exec x =>
    apply Ninst.effectRec_exec
    apply Xinst.balance_effectRec
  case push xs hxs =>
    apply Ninst.push_balance_effectRec

theorem Exec.balance_effect {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    Execution.Rel Devm.BalNoninc pre out :=
  Exec.effect balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2 Ninst.balance_effectRec Jinst.balance_effect Linst.balance_effect run

lemma Ninst.balance_effect (n : Ninst) : Ninst.Effect Devm.BalNoninc n := by
  apply Ninst.effect_of_effectRec balNoninc_refl_trans.2.1 balNoninc_refl_trans.2.2
  · exact Ninst.balance_effectRec
  · exact Jinst.balance_effect
  · exact Linst.balance_effect

theorem Func.balance_effect {fs : List Func} {sevm : Sevm}
    {pre post : Devm} {p : Func}
    (run : Func.Run fs sevm pre p post) : Devm.BalNoninc pre post := by
  apply Func.effect (R := Devm.BalNoninc) (htrans := balNoninc_refl_trans.2.2) _ _ Ninst.balance_effect Linst.balance_effect run
  · intro xs pr po hpop
    apply Devm.balNoninc_of_state
    rw [hpop.state]
    exact balNoninc_refl_trans.1.1 _
  · intro pr po hburn
    apply Devm.balNoninc_of_state
    rw [hburn.state]
    exact balNoninc_refl_trans.1.1 _

/-! ## 6. Executable wrappers and the Solvent.lean endpoint -/

lemma Xlot.balance_rel_of_filled {xl : Xlot}
    (hfill : xl.Filled) :
    Xlot.Rel Devm.BalNoninc xl := by
  rcases xl with _ | ⟨evm, exn⟩
  · constructor
  · rcases hfill with ⟨exc⟩
    exact Exec.balance_effect exc

lemma processMessage_balance_noninc {msg : Msg} {post : Devm}
    (h : processMessage msg = .ok post) :
    State.BalNoninc msg.benv.state post.state := by
  obtain ⟨xl, hfill, hrun⟩ := of_processMessage msg (.ok post) h
  have heff := ProcessMessage.balance_effect (Xlot.balance_rel_of_filled hfill) hrun
  change State.BalNoninc msg.benv.state post.state at heff
  exact heff

lemma processCreateMessage_balance_noninc
    {msg : Msg} {post : Devm}
    (h : processCreateMessage msg = .ok post) :
    State.BalNoninc msg.benv.state post.state := by
  rcases of_processCreateMessage msg (.ok post) h with ⟨xl, hfill, hrun⟩
  have hxl : Xlot.Rel Devm.BalNoninc xl := Xlot.balance_rel_of_filled hfill
  have heff := ProcessCreateMessage.balance_effect hxl hrun
  exact heff

lemma setDelegationStep_bal_eq {auth : Auth} {msg msg' : Msg} {rc rc' : B256}
    (h : setDelegationStep auth msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  unfold setDelegationStep at h
  dsimp only at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩; rfl
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, _⟩; rfl
      · cases h
      · split at h
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩; rfl
        · split at h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; rfl
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            show ((msg.benv.state.setCode _ _).incrNonce _).bal =
              msg.benv.state.bal
            rw [State.incrNonce_bal, State.setCode_bal]

lemma setDelegationLoop_bal_eq {auths : List Auth} {msg msg' : Msg}
    {rc rc' : B256}
    (h : setDelegationLoop auths msg rc = .ok ⟨msg', rc'⟩) :
    msg'.benv.state.bal = msg.benv.state.bal := by
  induction auths generalizing msg rc with
  | nil =>
    unfold setDelegationLoop at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | cons auth auths ih =>
    unfold setDelegationLoop at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i p h_step
      obtain ⟨msgS, rcS⟩ := p
      exact (ih h).trans (setDelegationStep_bal_eq h_step)

lemma setDelegation_balSum_eq {msg msg' : Msg} {refund : B256}
    (h : setDelegation msg = .ok ⟨msg', refund⟩) :
    State.balSum msg'.benv.state = State.balSum msg.benv.state := by
  unfold setDelegation at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p h_loop
    obtain ⟨msgL, rcL⟩ := p
    have h_bal := setDelegationLoop_bal_eq h_loop
    split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      unfold State.balSum
      rw [show ({ msgL with
        code := msgL.benv.state.getCode _ } : Msg).benv.state.bal =
          msgL.benv.state.bal from rfl, h_bal]

lemma processMessageCall.call_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (h : processMessageCall.call msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.call at h
  dsimp only at h
  split at h
  · simp only [bind, Except.bind] at h
    unfold Except.bimap at h
    split at h
    · injection h
    · rename_i evm h_evm
      split at h_evm
      · injection h_evm
      · rename_i evm' h_pm
        simp only [id_eq, Except.ok.injEq] at h_evm
        subst h_evm
        have hbal := processMessage_balance_noninc h_pm
        have hpre : State.BalNoninc msg.benv.state evm'.state := by
          split at hbal <;> exact hbal
        split at h
        · split at h
          · injection h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hpre
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact hpre
  · rcases h_del : setDelegation msg with ⟨err⟩ | ⟨⟨msgD, val⟩⟩
    · simp only [h_del, bind, Except.bind] at h
      injection h
    · simp only [h_del, bind, Except.bind] at h
      have h_sum := setDelegation_balSum_eq h_del
      unfold Except.bimap at h
      split at h
      · injection h
      · rename_i evm h_evm
        split at h_evm
        · injection h_evm
        · rename_i evm' h_pm
          simp only [id_eq, Except.ok.injEq] at h_evm
          subst h_evm
          have hbal := processMessage_balance_noninc h_pm
          have hpre : State.BalNoninc msg.benv.state evm'.state := by
            have hD : State.BalNoninc msgD.benv.state evm'.state := by
              split at hbal <;> exact hbal
            unfold State.BalNoninc at *
            omega
          split at h
          · split at h
            · injection h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩
              exact hpre
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hpre

lemma processMessageCall.create_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (h : processMessageCall.create msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall.create at h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩
    exact le_refl _
  · simp only [bind, Except.bind] at h
    unfold Except.bimap at h
    split at h
    · injection h
    · rename_i evm h_evm
      split at h_evm
      · injection h_evm
      · rename_i evm' h_pm
        simp only [id_eq, Except.ok.injEq] at h_evm
        subst h_evm
        have hbal := processCreateMessage_balance_noninc h_pm
        split at h
        · split at h
          · injection h
          · simp only [Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩
            exact hbal
        · simp only [Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact hbal

lemma processMessageCall_balance_noninc
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    State.BalNoninc msg.benv.state post := by
  unfold processMessageCall at h
  split at h
  · exact processMessageCall.create_balance_noninc h
  · exact processMessageCall.call_balance_noninc h

lemma processMessageCall_sum_le
    {msg : Msg} {post : Jaune.State} {out : MsgCallOutput}
    (h : processMessageCall msg = .ok ⟨post, out⟩) :
    sum post.bal ≤ sum msg.benv.state.bal := by
  exact processMessageCall_balance_noninc h


end Blanc
