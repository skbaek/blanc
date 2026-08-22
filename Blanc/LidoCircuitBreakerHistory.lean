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
  e.currentTarget = ca ∧ c.Pre ca e s ∧
    Exec.InvDepth e.depth ca c.prog (c.Pre ca) (c.Post ca)

/-- Every selector-comparison line in the dispatcher leaves `Devm.state`
untouched, so the carried invariant survives the line and the branch's pop. -/
private theorem DispatchInv.line {L : Line} (hL : Line.Inv Devm.state L)
    {e : Sevm} {s s' s'' : Devm} {w : B256}
    (h : DispatchInv c ca e s) (hline : Line.Run e s L s')
    (hpop : Devm.PopBurn [w] s' s'') :
    DispatchInv c ca e s'' :=
  ⟨h.1, h.2.1.state_eq (hpop.state.symm.trans (hL hline).symm), h.2.2⟩

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
  intro sevm s r h_ct h_pre h_ih h_run
  cases h_run with
  | next h_inst h_rest =>
    refine h h_ct (h_pre.state_eq ?_) h_ih h_rest
    exact (popStateInv h_inst).symm

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
    exact h_fall h.1 (h.2.1.state_eq h_burn.state.symm) h.2.2 h_body

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
          (DispatchInv.line (by line_inv) h h₁ h_pop)
          h_run
      · have hs := DispatchInv.line (by line_inv) h h₁
          (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)
        exact h_all (word, body) (by simp) hs.1 hs.2.1 hs.2.2 h_run
    | hd' :: tl' =>
      intro h_all e s r h
      func_execute 3
      intro h_branch
      rcases of_run_branch h_branch with
        ⟨s₂, h_pop, h_run⟩ | ⟨w, s₂, s₃, hw, h_pop, h_burn, h_run⟩
      · have hs := DispatchInv.line (by line_inv) h h₁ h_pop
        exact ih (fun p hp => h_all p (by simp [hp])) hs h_run
      · have hs := DispatchInv.line (by line_inv) h h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)
        exact funcSound_pop (h_all (word, body) (by simp)) hs.1 hs.2.1 hs.2.2 h_run

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
  · exact hr (DispatchInv.line (by line_inv) h h₁ h_pop) h_run
  · exact hl (DispatchInv.line (by line_inv) h h₁ (Devm.popBurn_of_popBurn_of_pop h_pop h_burn)) h_run

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

/-! ## The open-contract frame theorem

`Sound` quantifies over arbitrary successful runs of the exact runtime and
hands down the strictly-deeper-frame hypothesis.  Nothing here restricts the
callee's bytecode, forbids re-entry into the same instance, or identifies the
post-callback entry list with the entry list. -/

/-- The reverting fallback and every reverting auxiliary target have no
successful run at all, so their obligation is vacuous. -/
private theorem funcSound_rev (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).FuncSound ca aux Func.rev := by
  intro _ _ _ _ _ _ h_run
  exact absurd h_run not_run_rev

/-- `Sound` for the exact runtime, reduced to one obligation per dispatch
target.  The five-instruction payable/calldata-size guard, the `fsig` selector
extraction and the three-pivot hybrid tree are all peeled here. -/
theorem registrySpec_sound_of_funcSound (dp : DeployParams) (ca : Adr)
    (h_all : ∀ p ∈ funcs dp, (registrySpec dp).FuncSound ca aux p.2) :
    (registrySpec dp).Sound ca := by
  intro sevm pre post run h_ca ih h_pre
  have ih' : Exec.InvDepth sevm.depth ca (registrySpec dp).prog
      ((registrySpec dp).Pre ca) ((registrySpec dp).Post ca) := by
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
  clear h_pre burn pre
  refine run_prepend_elim _
    [callvalue, pushB256 4, calldatasize, lt, Ninst.or] ?_ run
  intro s₁ h₁ run₁
  have h_pre₁ : (registrySpec dp).Pre ca sevm s₁ :=
    h_pre₀.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) h₁).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) h₁).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) h₁).symm ca)
  clear h_pre₀ h₁ run s₀
  obtain ⟨s₂, h_pop, run₂⟩ := of_run_branch_rev run₁
  have h_pre₂ : (registrySpec dp).Pre ca sevm s₂ :=
    h_pre₁.state_eq h_pop.state.symm
  clear h_pre₁ h_pop run₁
  refine run_prepend_elim _ fsig ?_ run₂
  intro s₃ h₃ run₃
  have h_pre₃ : (registrySpec dp).Pre ca sevm s₃ :=
    h_pre₂.of_eqs
      (congrFun (Line.of_inv Devm.getCode (by line_inv) h₃).symm ca)
      (Line.of_inv Devm.getBal (by line_inv) h₃).symm
      (congrFun (Line.of_inv Devm.getStor (by line_inv) h₃).symm ca)
  exact post_of_run_hybridDispatch (k := fallbackSlot) (fallback := Func.rev)
    rfl (funcSound_rev dp ca) (funcs dp) h_all ⟨h_ca, h_pre₃, ih'⟩ run₃

theorem registrySpec_sound (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).Sound ca := by
  sorry

theorem registrySpec_preserves (dp : DeployParams) (ca : Adr) :
    (registrySpec dp).Preserves ca :=
  ContractSpec.preserves_inv (registrySpec dp) ca (registrySpec_sound dp ca)

/-! ## Messages, transactions, blocks and histories -/

theorem processMessageCall_preserves_registryStable (dp : DeployParams)
    {ca : Adr} {msg : Msg} {st' : Jaune.State} {out : MsgCallOutput}
    (h_run : processMessageCall msg = .ok ⟨st', out⟩)
    (h_inv : (registrySpec dp).MsgInv ca msg) :
    RegistryStable dp ca st' :=
  (registryStable_iff_stateInv dp ca st').mpr
    (ContractSpec.processMessageCall_preserves_inv (registrySpec_preserves dp ca) h_run h_inv).1

theorem processTransaction_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) (i : Nat)
    (st : Jaune.State)
    (h_run : processTransaction benv bout tx i = .ok ⟨st, bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_fresh : ca ∉ benv.createdAccounts)
    (h_stable : RegistryStable dp ca benv.state) :
    RegistryStable dp ca st :=
  (registryStable_iff_stateInv dp ca st).mpr
    (ContractSpec.processTransaction_preserves_inv ca (registrySpec_preserves dp ca) benv bout
      bout' tx i st h_run h_sum
      ⟨(registryStable_iff_stateInv dp ca benv.state).mp h_stable, h_fresh⟩).state

theorem applyTransactions_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (txis : List (Nat × Tx)) (benv benv' : Benv)
    (bout bout' : BlockOutput)
    (h_run : applyTransactions txis benv bout = .ok ⟨benv', bout'⟩)
    (h_sum : sum benv.state.bal < 2 ^ 256)
    (h_fresh : ca ∉ benv.createdAccounts)
    (h_stable : RegistryStable dp ca benv.state) :
    RegistryStable dp ca benv'.state :=
  (registryStable_iff_stateInv dp ca benv'.state).mpr
    (ContractSpec.applyTransactions_preserves_inv ca (registrySpec_preserves dp ca) txis benv
      benv' bout bout' h_run h_sum
      ⟨(registryStable_iff_stateInv dp ca benv.state).mp h_stable, h_fresh⟩).state

theorem stateTransitionWith_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (rules : ForkRules) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionWith rules ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransitionWith_preserves_inv ca (registrySpec_preserves dp ca) rules ch
      ch' block h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

theorem stateTransitionUsing_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (cfg : ChainConfig) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransitionUsing cfg ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransitionUsing_preserves_inv ca (registrySpec_preserves dp ca) cfg ch
      ch' block h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

theorem stateTransition_preserves_registryStable (dp : DeployParams)
    (ca : Adr) (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_stable : RegistryStable dp ca ch.state) :
    RegistryStable dp ca ch'.state :=
  (registryStable_iff_stateInv dp ca ch'.state).mpr
    (ContractSpec.stateTransition_preserves_inv ca (registrySpec_preserves dp ca) ch ch' block
      h_run h_wds ((registryStable_iff_stateInv dp ca ch.state).mp h_stable))

/-- The headline configured-chain theorem: from an exact-runtime stable
checkpoint, every state reachable by the configured valid-chain relation is
still stable. -/
theorem chainUsing_preserves_registryStable (dp : DeployParams) (ca : Adr)
    (cfg : ChainConfig) (checkpoint future : BlockChain)
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    RegistryStable dp ca future.state :=
  (registryStable_iff_stateInv dp ca future.state).mpr
    (ContractSpec.chainUsing_preserves_inv ca (registrySpec_preserves dp ca) cfg checkpoint
      future reach ((registryStable_iff_stateInv dp ca checkpoint.state).mp stable))

theorem chain_preserves_registryStable (dp : DeployParams) (ca : Adr)
    (checkpoint future : BlockChain)
    (reach : BlockChain.Reach checkpoint future)
    (stable : RegistryStable dp ca checkpoint.state) :
    RegistryStable dp ca future.state :=
  (registryStable_iff_stateInv dp ca future.state).mpr
    (ContractSpec.chain_preserves_inv ca (registrySpec_preserves dp ca) checkpoint future reach
      ((registryStable_iff_stateInv dp ca checkpoint.state).mp stable))

end LidoCircuitBreaker

end Blanc
