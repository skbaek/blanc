import Blanc.LidoCircuitBreakerSuccess

/-!
# Registry integrity through arbitrary histories

Stage 7, first cut.  The Registry goals prove that individual exact mutations
preserve `RegistryWitness` at named stable boundaries.  This module supplies the
induction principle that joins them: a storage-only coherent state, packaged as
a `ContractSpec`, carried through every exact runtime frame and then lifted by
the generic ladder to messages, transactions, blocks and chain reachability.

The invariant is deliberately *existential* in the entry list.  A callback that
re-enters the CircuitBreaker as admin may register a pauser, so the list a
frame returns need not be the list it entered with.  Requiring the same list
would be a false strengthening.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoCircuitBreaker

/-- A storage image is *Registry-coherent* when some ordered entry list
witnesses every projected Registry region of it.  This is exactly the existing
`RegistryWitness`, existentially closed; no field is added and none changes
meaning. -/
def RegistryCoherent (s : Stor) : Prop :=
  ∃ entries, RegistryWitness (logicalStorageOfStor s) entries

/-- The Lido CircuitBreaker contract specification.  Storage-only: the
invariant ignores the callvalue in flight and the contract's ETH balance, so
the balance side condition is trivial and every balance-movement slot is
discharged by the fact that `subBal`/`addBal` do not touch storage. -/
def registrySpec (dp : DeployParams) : ContractSpec where
  prog := runtime dp
  Inv := fun s _ _ => RegistryCoherent s
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun h _ => h
  inv_recv := fun h _ => h
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub h_ne _ h_inv
    show RegistryCoherent _
    have h_stor : (st'.addBal callee wad).getStor ca = st.getStor ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      show ((st'.setBal callee _).get ca).stor = (st.get ca).stor
      rw [State.setBal_get_stor, h_st', State.setBal_get_stor]
    rw [h_stor]
    exact h_inv
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub h_ne _ h_inv
    show RegistryCoherent _
    have h_stor : (st'.addBal ca wad).getStor ca = st.getStor ca := by
      rcases State.of_subBal h_sub with ⟨-, h_st'⟩
      show ((st'.setBal ca _).get ca).stor = (st.get ca).stor
      rw [State.setBal_get_stor, h_st', State.setBal_get_stor]
    rw [h_stor]
    exact h_inv
  inv_addBal := by
    intro w ca a val v _ _ h_inv
    show RegistryCoherent _
    have h_stor : (w.addBal a val).getStor ca = w.getStor ca := by
      show ((w.setBal a _).get ca).stor = (w.get ca).stor
      rw [State.setBal_get_stor]
    rw [h_stor]
    exact h_inv

/-- The reader-facing stable checkpoint: the exact compiled runtime is
installed at `ca`, and `ca`'s actual storage is Registry-coherent. -/
structure RegistryStable (dp : DeployParams) (ca : Adr)
    (w : Jaune.State) : Prop where
  code : some (w.getCode ca).toList = Prog.compile (runtime dp)
  coherent : RegistryCoherent (w.getStor ca)

theorem registryStable_iff_stateInv (dp : DeployParams) (ca : Adr)
    (w : Jaune.State) :
    RegistryStable dp ca w ↔ (registrySpec dp).StateInv ca w :=
  ⟨fun h => ⟨h.code, trivial, h.coherent⟩, fun h => ⟨h.code, h.inv⟩⟩

/-! ## The exact hybrid dispatcher

`runtime dp` is neither of the two dispatcher shapes the generic ladder
supports: its main is a five-instruction payable/calldata-size guard over
`fsig +++ hybridDispatchWith fallbackSlot (funcs dp)`, and the dispatcher
itself is three `splitDispatch` pivots over four `linearDispatchWith` chains.
The production artifact does not move to fit a generic theorem, so the join is
proved here, against the exact emitted shape.

A lemma naming `hybridDispatchWith` cannot live in a shared module: the
dispatcher is defined in a contract module, and a shared module importing it
would invert the import hierarchy.  These reductions are therefore
contract-local by construction, not by preference. -/

section Dispatch

variable {c : ContractSpec} {ca : Adr} {k : Nat} {aux : List Func}

/-- The invariant carried across the dispatcher's scratch lines: this frame is
the contract, the precondition holds, and the deeper-frame hypothesis is in
hand. -/
private def DispatchInv (c : ContractSpec) (ca : Adr) (e : Sevm) (s : Devm) : Prop :=
  e.currentTarget = ca ∧ c.Pre ca e s ∧ Mem.Wf s.memory ∧
    Exec.InvDepth e.depth ca c.prog (c.PreWf ca) (c.Post ca)

/-- Every selector-comparison line in the dispatcher leaves `Devm.state`
untouched, so the carried invariant survives the line and the branch's pop. -/
private theorem DispatchInv.line {L : Line} (hL : Line.Inv Devm.state L)
    (hM : Line.Inv Devm.memory L)
    {e : Sevm} {s s' s'' : Devm} {w : B256}
    (h : DispatchInv c ca e s) (hline : Line.Run e s L s')
    (hpop : Devm.PopBurn [w] s' s'') :
    DispatchInv c ca e s'' :=
  ⟨h.1, h.2.1.state_eq (hpop.state.symm.trans (hL hline).symm),
    ((hM hline).trans hpop.memory) ▸ h.2.2.1, h.2.2.2⟩

/-- `pop` is neither `SSTORE` nor `TSTORE`, so it leaves the world state alone. -/
private theorem popStateInv : Ninst.Inv Devm.state pop := by
  intro e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
  exact Rinst.preserves_state (by intro hc; cases hc) (by intro hc; cases hc) run.2.symm

/-- A `pop` in front of a dispatch target is storage-silent, so the target's
own obligation is enough. -/
private theorem funcSound_pop {f : Func} (h : c.FuncSound ca aux f) :
    c.FuncSound ca aux (pop ::: f) := by
  intro sevm s r h_ct h_pre h_wf h_ih h_run
  cases h_run with
  | next h_inst h_rest =>
    refine h h_ct (h_pre.state_eq ?_) ?_ h_ih h_rest
    · exact (popStateInv h_inst).symm
    · rw [← Ninst.Hinv.inv (f := Devm.memory) h_inst]; exact h_wf

/-- Reaching the indexed miss target. -/
private theorem post_of_run_call {fallback : Func}
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_fall : c.FuncSound ca aux fallback)
    {e : Sevm} {s r : Devm} (h : DispatchInv c ca e s)
    (h_run : Func.Run (c.prog.main :: aux) e s (.call k) r) :
    c.Post ca e r := by
  cases h_run with
  | call h_eq h_burn h_body =>
    have hf := Option.some.inj (h_fb.symm.trans h_eq)
    subst hf
    exact h_fall h.1 (h.2.1.state_eq h_burn.state.symm)
      (h_burn.memory ▸ h.2.2.1) h.2.2.2 h_body

/-- One linear equality chain: a successful walk reaches one of its listed
targets or the indexed fallback. -/
private theorem post_of_run_linearDispatch {fallback : Func}
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_fall : c.FuncSound ca aux fallback) :
    ∀ entries : List (B256 × Func),
      (∀ p ∈ entries, c.FuncSound ca aux p.2) →
      ∀ {e : Sevm} {s r : Devm}, DispatchInv c ca e s →
        Func.Run (c.prog.main :: aux) e s (linearDispatchWith k entries) r →
        c.Post ca e r := by
  intro entries
  induction entries with
  | nil =>
    intro _ e s r h h_run
    exact post_of_run_call h_fb h_fall h h_run
  | cons hd tl ih =>
    obtain ⟨word, body⟩ := hd
    match tl with
    | [] =>
      intro h_all e s r h
      func_execute 2
      intro h_branch
      rcases of_run_branch h_branch with
        ⟨s₂, h_pop, h_run⟩ | ⟨w, s₂, s₃, hw, h_pop, h_burn, h_run⟩
      · exact post_of_run_call h_fb h_fall
          (DispatchInv.line (by line_inv) (by line_inv) h h₁ h_pop)
          h_run
      · have hs := DispatchInv.line (by line_inv) (by line_inv) h h₁
          (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)
        exact h_all (word, body) (by simp) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 h_run
    | hd' :: tl' =>
      intro h_all e s r h
      func_execute 3
      intro h_branch
      rcases of_run_branch h_branch with
        ⟨s₂, h_pop, h_run⟩ | ⟨w, s₂, s₃, hw, h_pop, h_burn, h_run⟩
      · have hs := DispatchInv.line (by line_inv) (by line_inv) h h₁ h_pop
        exact ih (fun p hp => h_all p (by simp [hp])) hs h_run
      · have hs := DispatchInv.line (by line_inv) (by line_inv) h h₁
          (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)
        exact funcSound_pop (h_all (word, body) (by simp))
          hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 h_run

/-- One balanced pivot. -/
private theorem post_of_run_splitDispatch {left right : Func} {pivot : B256}
    (hl : ∀ {e : Sevm} {s r : Devm}, DispatchInv c ca e s →
      Func.Run (c.prog.main :: aux) e s left r → c.Post ca e r)
    (hr : ∀ {e : Sevm} {s r : Devm}, DispatchInv c ca e s →
      Func.Run (c.prog.main :: aux) e s right r → c.Post ca e r)
    {e : Sevm} {s r : Devm} (h : DispatchInv c ca e s)
    (h_run : Func.Run (c.prog.main :: aux) e s
      (splitDispatch pivot left right) r) :
    c.Post ca e r := by
  revert h_run
  func_execute 3
  intro h_branch
  rcases of_run_branch h_branch with
    ⟨s₂, h_pop, h_run⟩ | ⟨w, s₂, s₃, hw, h_pop, h_burn, h_run⟩
  · exact hr (DispatchInv.line (by line_inv) (by line_inv) h h₁ h_pop) h_run
  · exact hl (DispatchInv.line (by line_inv) (by line_inv) h h₁
      (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run

/-- The whole three-pivot / four-chain dispatcher. -/
private theorem post_of_run_hybridDispatch {fallback : Func}
    (h_fb : (c.prog.main :: aux)[k]? = some fallback)
    (h_fall : c.FuncSound ca aux fallback)
    (entries : List (B256 × Func))
    (h_all : ∀ p ∈ entries, c.FuncSound ca aux p.2)
    {e : Sevm} {s r : Devm} (h : DispatchInv c ca e s)
    (h_run : Func.Run (c.prog.main :: aux) e s
      (hybridDispatchWith k entries) r) :
    c.Post ca e r := by
  have hline : ∀ (m n : Nat), ∀ p ∈ (entries.drop m).take n,
      c.FuncSound ca aux p.2 := by
    intro m n p hp
    exact h_all p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
  have hdrop : ∀ (m : Nat), ∀ p ∈ entries.drop m, c.FuncSound ca aux p.2 := by
    intro m p hp
    exact h_all p (List.mem_of_mem_drop hp)
  have htake : ∀ (n : Nat), ∀ p ∈ entries.take n, c.FuncSound ca aux p.2 := by
    intro n p hp
    exact h_all p (List.mem_of_mem_take hp)
  refine post_of_run_splitDispatch ?_ ?_ h h_run
  · exact fun h' hr' => post_of_run_splitDispatch
      (fun h'' hr'' =>
        post_of_run_linearDispatch h_fb h_fall _ (htake 5) h'' hr'')
      (fun h'' hr'' =>
        post_of_run_linearDispatch h_fb h_fall _ (hline 5 4) h'' hr'')
      h' hr'
  · exact fun h' hr' => post_of_run_splitDispatch
      (fun h'' hr'' =>
        post_of_run_linearDispatch h_fb h_fall _ (hline 9 4) h'' hr'')
      (fun h'' hr'' =>
        post_of_run_linearDispatch h_fb h_fall _ (hdrop 13) h'' hr'')
      h' hr'

end Dispatch

/-! ## Storage-silent bodies

`Func.Inv` quantifies over the context list, so it refuses a tail jump: the
callee is arbitrary at that altitude.  Every Lido view tail-jumps to the
empty-revert slot, and `getPausables` tail-jumps to itself.  `StorFixed` is the
same property stated with the exact runtime context fixed, which is what lets a
jump be discharged by the slot it actually reaches. -/

/-- A body that changes no account's persistent storage on any successful run
in the exact runtime context. -/
def StorFixed (dp : DeployParams) (f : Func) : Prop :=
  ∀ {sevm : Sevm} {s r : Devm},
    Func.Run ((runtime dp).main :: aux) sevm s f r →
    Devm.getStor r = Devm.getStor s

namespace StorFixed

variable {dp : DeployParams}

theorem of_inv {f : Func} (h : Func.Inv Devm.getStor Devm.getStor f) :
    StorFixed dp f := fun hr => (h hr).symm

/-- A terminal instruction other than `JUMPDEST` cannot write storage. -/
theorem last {l : Linst} (h : Linst.Inv Devm.getStor Devm.getStor l) :
    StorFixed dp (.last l) := of_inv (last_inv h)

theorem prepend {l : Line} {f : Func} (hl : Line.Inv Devm.getStor l)
    (hf : StorFixed dp f) : StorFixed dp (l +++ f) := by
  intro sevm s r h
  rcases of_run_prepend _ _ h with ⟨s', hl', hf'⟩
  exact (hf hf').trans (hl hl').symm

theorem next {i : Ninst} {f : Func} [Ninst.Hinv Devm.getStor i]
    (hf : StorFixed dp f) : StorFixed dp (i ::: f) := by
  intro sevm s r h
  cases h with
  | next hi hrest =>
    exact (hf hrest).trans (Ninst.Hinv.inv (f := Devm.getStor) hi).symm

theorem branch {f g : Func} (hf : StorFixed dp f) (hg : StorFixed dp g) :
    StorFixed dp (Func.branch f g) := by
  intro sevm s r h
  rcases of_run_branch h with
    ⟨s', hpb, hrun⟩ | ⟨w, s', s'', hw, hpb, hb, hrun⟩
  · exact (hf hrun).trans (funext (getStor_eq_of_state_eq hpb.state.symm))
  · refine (hg hrun).trans (funext (getStor_eq_of_state_eq ?_))
    exact (hpb.state.trans hb.state).symm

theorem call {k : Nat} {g : Func}
    (hk : ((runtime dp).main :: aux)[k]? = some g) (hg : StorFixed dp g) :
    StorFixed dp (.call k) := by
  intro sevm s r h
  cases h with
  | call hget hburn hrun =>
    have heq := Option.some.inj (hk.symm.trans hget)
    subst heq
    exact (hg hrun).trans (funext (getStor_eq_of_state_eq hburn.state.symm))

/-- `Func.revert` has no successful run at all. -/
theorem revert : StorFixed dp Func.revert := fun h => absurd h not_run_revert

end StorFixed

/-- A storage-silent body satisfies its `FuncSound` obligation outright: the
invariant is a predicate on the contract's storage, the side condition is
trivial, and the deeper-frame hypothesis is not needed. -/
theorem funcSound_of_storFixed {dp : DeployParams} {ca : Adr} {f : Func}
    (h : StorFixed dp f) : (registrySpec dp).FuncSound ca aux f := by
  intro sevm s r h_ct h_pre _ _ h_run
  subst h_ct
  refine ⟨trivial, ?_⟩
  show RegistryCoherent (Devm.getStor r sevm.currentTarget)
  rw [h h_run]
  exact h_pre.inv.1 rfl

/-- The program-free core: a body that maps Registry-coherent storage at the
active target to Registry-coherent storage.  This is the obligation shape for a
target whose writes are real but land outside every Registry region. -/
theorem funcSound_of_registryCore {dp : DeployParams} {ca : Adr} {f : Func}
    (h : Func.Core ((runtime dp).main :: aux) RegistryCoherent f) :
    (registrySpec dp).FuncSound ca aux f :=
  ContractSpec.funcSound_of_core (fun _ => trivial) (fun h => h) h

/-! ## The open-contract frame theorem

`Sound` quantifies over arbitrary successful runs of the exact runtime and
hands down the strictly-deeper-frame hypothesis.  Nothing here restricts the
callee's bytecode, forbids re-entry into the same instance, or identifies the
post-callback entry list with the entry list. -/

/-- The reverting fallback and every reverting auxiliary target have no
successful run at all, so their obligation is vacuous. -/
private theorem funcSound_revert (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux Func.revert := by
  intro _ _ _ _ _ _ _ h_run
  exact absurd h_run not_run_revert

/-- `Sound` for the exact runtime, reduced to one obligation per dispatch
target.  The five-instruction payable/calldata-size guard, the `fsig` selector
extraction and the three-pivot hybrid tree are all peeled here. -/
theorem registrySpec_sound_of_funcSound (dp : DeployParams) (ca : Adr)
    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :
    (registrySpec dp).Sound ca := by
  intro sevm pre post run h_ca ih h_wf h_pre
  have ih' : Exec.InvDepth sevm.depth ca (registrySpec dp).prog
      ((registrySpec dp).PreWf ca) ((registrySpec dp).Post ca) := by
    intro pc' sevm' devm' exn'
    cases exn'
    · simp only [ifOk, implies_true]
    · apply ih
  clear ih
  dsimp only [Prog.Run] at run
  cases run
  rename (_ = _) => h_eq
  rename (Func.Run _ _ _ _ _) => run
  rename (Devm.Burn _ _) => burn
  rename Devm => s₀
  cases h_eq
  have h_pre₀ : (registrySpec dp).Pre ca sevm s₀ := h_pre.state_eq burn.state.symm
  have h_wf₀ : Mem.Wf s₀.memory := by rw [← burn.memory]; exact h_wf
  clear h_pre h_wf burn pre
  refine run_prepend_elim _
    [callvalue, pushB256 4, calldatasize, lt, Ninst.or] ?_ run
  intro s₁ h₁ run₁
  have h_pre₁ : (registrySpec dp).Pre ca sevm s₁ :=
    h_pre₀.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) h₁).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) h₁).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) h₁).symm ca)
  have h_wf₁ : Mem.Wf s₁.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) h₁]; exact h_wf₀
  clear h_pre₀ h_wf₀ h₁ run s₀
  obtain ⟨s₂, h_pop, run₂⟩ := of_run_branch_revert run₁
  have h_pre₂ : (registrySpec dp).Pre ca sevm s₂ :=
    h_pre₁.state_eq h_pop.state.symm
  have h_wf₂ : Mem.Wf s₂.memory := by rw [← h_pop.memory]; exact h_wf₁
  clear h_pre₁ h_wf₁ h_pop run₁
  refine run_prepend_elim _ fsig ?_ run₂
  intro s₃ h₃ run₃
  have h_pre₃ : (registrySpec dp).Pre ca sevm s₃ :=
    h_pre₂.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) h₃).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) h₃).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) h₃).symm ca)
  have h_wf₃ : Mem.Wf s₃.memory := by
    rw [← Line.of_inv Devm.memory (by line_inv) h₃]; exact h_wf₂
  exact post_of_run_hybridDispatch (k := fallbackSlot) (fallback := Func.revert)
    rfl (funcSound_revert dp ca) (funcs dp) h_all ⟨h_ca, h_pre₃, h_wf₃, ih'⟩ run₃

end LidoCircuitBreaker

end Blanc
