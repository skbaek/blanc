import Blanc.ExecutionInRawNodes
import Blanc.ExecutionInCellProvenance

/-!
# How each raw node of an In-history is reached

`Exec.rawNodes` lists every reached driver node in execution order, and the
history chronology (`ConfiguredHistoryTraceIn.rawNodes`) concatenates those
lists. Each listed node `n`, at a positional split `before ++ n :: after`, is
reached in one of three ways (`RawOrigin before n`):

* it is a message root that runs the code installed at its own target
  (`RootOwnCode n`): for every address holding nonempty code that is no
  EIP-7702 designator, a root targeting it runs that code;
* an earlier node runs in the same frame (`∃ m ∈ before, m.sevm = n.sevm`);
* an earlier node spawned it (`∃ m ∈ before, Exec.Deriv.SpawnedAt m n`).

`List.forall_mem_of_positional` is the strong induction along positions that
consumes it. `OriginList L` says this holds at every positional split of `L`; it is closed
under `++` (`OriginList.append`). The level-zero fact is
`Exec.rawNodes_split_origin` (by induction on the run); the message wrappers
supply `RootOwnCode` at their retained roots from the message they enter:
a transaction's call message and a system message run their target's code
(`MsgOwn`), the EIP-7702 authorization prefix and code-delegation resolution
keep that unless the target's code is a designator, and a CREATE root targets
an address without code. `ConfiguredHistoryTraceIn.rawNodes_origin` is the
history form.

Contract-neutral; no premise beyond the trace itself.

Reused (not copied): `Frame.enter_run_code`, `Frame.enter_run_currentTarget`,
`Frame.enter_run_getCode`, `RunFrame.some_inv`,
`processCreateMessage.msg_getCode`, `ne_wa_of_not_hasCodeOrNonce`,
`setDelegationLoop_fields`, `messageCallDelegation_fields`,
`prepareMessage_own_entry`, `systemTransactionMessage_benv_state`,
`List.split_append_cons`.
-/

namespace Blanc

open Jaune

/-- **Strong induction along positions.** A property that holds at each element once it
holds at every strictly earlier element (positionally: values may repeat) holds at every
element. -/
theorem List.forall_mem_of_positional {α : Type} {L : List α} {Q : α → Prop}
    (step : ∀ before n after, L = before ++ n :: after → (∀ m ∈ before, Q m) → Q n) :
    ∀ n ∈ L, Q n := by
  suffices h : ∀ k before n after, L = before ++ n :: after → before.length = k → Q n by
    intro n hn
    obtain ⟨before, after, split⟩ := List.append_of_mem hn
    exact h _ before n after split rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro before n after split hlen
    refine step before n after split fun m hm => ?_
    obtain ⟨b₁, b₂, hb⟩ := List.append_of_mem hm
    refine ih b₁.length ?_ b₁ m (b₂ ++ n :: after) ?_ rfl
    · rw [← hlen, hb]; simp only [List.length_append, List.length_cons]; omega
    · rw [split, hb]; simp only [List.append_assoc, List.cons_append]

namespace Exec.Deriv

/-- `n` is the root of a child frame entered at `m`. -/
def SpawnedAt (m n : Exec.Deriv) : Prop :=
  ∃ (f : Frame) (rsm : Resume) (pc' : Nat) (cevm : Evm),
    Evm.step ⟨m.pc, m.sevm, m.devm⟩ = .spawn f rsm pc' ∧ f.enter = .run cevm ∧
      cevm.pc = n.pc ∧ cevm.sta = n.sevm ∧ cevm.dyna = n.devm

end Exec.Deriv

namespace ExecutionTrace

/-- A root that runs the code installed at its own target whenever that code is
nonempty and no EIP-7702 designator. -/
def RootOwnCode (n : Exec.Deriv) : Prop :=
  ∀ wa, n.sevm.currentTarget = wa → (n.devm.getCode wa).toList ≠ [] →
    ¬ isValidDelegation (n.devm.getCode wa) → n.sevm.code = n.devm.getCode wa

/-- How the node `n` after the nodes `before` is reached. -/
def RawOrigin (before : List Exec.Deriv) (n : Exec.Deriv) : Prop :=
  RootOwnCode n ∨ (∃ m ∈ before, m.sevm = n.sevm) ∨
    ∃ m ∈ before, Exec.Deriv.SpawnedAt m n

/-- Every positional split of `L` has a reached node. -/
def OriginList (L : List Exec.Deriv) : Prop :=
  ∀ before n after, L = before ++ n :: after → RawOrigin before n

theorem RawOrigin.mono_left {before : List Exec.Deriv} {n : Exec.Deriv}
    (h : RawOrigin before n) (pre : List Exec.Deriv) : RawOrigin (pre ++ before) n := by
  rcases h with h | ⟨m, hm, he⟩ | ⟨m, hm, hs⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨m, List.mem_append_right pre hm, he⟩)
  · exact Or.inr (Or.inr ⟨m, List.mem_append_right pre hm, hs⟩)

theorem OriginList.nil : OriginList [] := by
  intro before n after h
  have := congrArg List.length h
  simp only [List.length_nil, List.length_append, List.length_cons] at this
  omega

theorem OriginList.append {L L' : List Exec.Deriv} (h : OriginList L) (h' : OriginList L') :
    OriginList (L ++ L') := by
  intro before n after split
  rcases List.split_append_cons split with ⟨m, hX, -⟩ | ⟨nb, hb, hY⟩
  · exact h before n m hX
  · rw [hb]
    exact (h' nb n after hY).mono_left L

/-- **Level zero.** Every node of a run is its root, follows an earlier node of
its frame, or was spawned by an earlier node. -/
theorem Exec.rawNodes_split_origin :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      {before after : List Exec.Deriv} {n : Exec.Deriv},
      Exec.rawNodes run = before ++ n :: after →
      (before = [] ∧ n = ⟨pc, sevm, pre, out, run⟩) ∨
        (∃ m ∈ before, m.sevm = n.sevm) ∨ ∃ m ∈ before, Exec.Deriv.SpawnedAt m n := by
  intro pc sevm pre out run
  induction run with
  | halt h =>
      intro before after n split
      simp only [Exec.rawNodes] at split
      rcases before with _ | ⟨b, bs⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        exact Or.inl ⟨rfl, split.1.symm⟩
      · simp only [List.cons_append, List.cons.injEq] at split
        have := congrArg List.length split.2
        simp only [List.length_nil, List.length_append, List.length_cons] at this
        omega
  | doneErr h1 h2 h3 =>
      intro before after n split
      simp only [Exec.rawNodes] at split
      rcases before with _ | ⟨b, bs⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        exact Or.inl ⟨rfl, split.1.symm⟩
      · simp only [List.cons_append, List.cons.injEq] at split
        have := congrArg List.length split.2
        simp only [List.length_nil, List.length_append, List.length_cons] at this
        omega
  | @cont pc sevm devm pc' devm' ex step next ih =>
      intro before after n split
      simp only [Exec.rawNodes] at split
      rcases before with _ | ⟨b, bs⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        exact Or.inl ⟨rfl, split.1.symm⟩
      · simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, hrest⟩ := split
        rcases ih hrest with ⟨rfl, rfl⟩ | ⟨m, hm, he⟩ | ⟨m, hm, hs⟩
        · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
        · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ hm, he⟩)
        · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ hm, hs⟩)
  | @doneOk pc sevm devm f rsm pc' r devm' ex step enter resume next ih =>
      intro before after n split
      simp only [Exec.rawNodes] at split
      rcases before with _ | ⟨b, bs⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        exact Or.inl ⟨rfl, split.1.symm⟩
      · simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, hrest⟩ := split
        rcases ih hrest with ⟨rfl, rfl⟩ | ⟨m, hm, he⟩ | ⟨m, hm, hs⟩
        · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
        · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ hm, he⟩)
        · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ hm, hs⟩)
  | @runErr pc sevm devm f rsm pc' cevm raw e step enter child resume ih =>
      intro before after n split
      simp only [Exec.rawNodes] at split
      rcases before with _ | ⟨b, bs⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        exact Or.inl ⟨rfl, split.1.symm⟩
      · simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, hrest⟩ := split
        rcases ih hrest with ⟨rfl, rfl⟩ | ⟨m, hm, he⟩ | ⟨m, hm, hs⟩
        · exact Or.inr (Or.inr ⟨_, List.mem_cons_self,
            f, rsm, pc', cevm, step, enter, rfl, rfl, rfl⟩)
        · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ hm, he⟩)
        · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ hm, hs⟩)
  | @runOk pc sevm devm f rsm pc' cevm raw devm' ex step enter child resume next childIh
      nextIh =>
      intro before after n split
      simp only [Exec.rawNodes] at split
      rcases before with _ | ⟨b, bs⟩
      · simp only [List.nil_append, List.cons.injEq] at split
        exact Or.inl ⟨rfl, split.1.symm⟩
      · simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, hrest⟩ := split
        rcases List.split_append_cons hrest with ⟨m', hX, -⟩ | ⟨nb, hb, hY⟩
        · rcases childIh hX with ⟨rfl, rfl⟩ | ⟨m, hm, he⟩ | ⟨m, hm, hs⟩
          · exact Or.inr (Or.inr ⟨_, List.mem_cons_self,
              f, rsm, pc', cevm, step, enter, rfl, rfl, rfl⟩)
          · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ hm, he⟩)
          · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ hm, hs⟩)
        · subst hb
          rcases nextIh hY with ⟨rfl, rfl⟩ | ⟨m, hm, he⟩ | ⟨m, hm, hs⟩
          · exact Or.inr (Or.inl ⟨_, List.mem_cons_self, rfl⟩)
          · exact Or.inr (Or.inl ⟨m, List.mem_cons_of_mem _ (List.mem_append_right _ hm), he⟩)
          · exact Or.inr (Or.inr ⟨m, List.mem_cons_of_mem _ (List.mem_append_right _ hm), hs⟩)

/-- A run whose root runs its target's own code has an origin at every node. -/
theorem Exec.rawNodes_origin {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (root : RootOwnCode ⟨pc, sevm, pre, out, run⟩) :
    OriginList (Exec.rawNodes run) := by
  intro before n after split
  rcases Exec.rawNodes_split_origin run split with ⟨-, rfl⟩ | h | h
  · exact Or.inl root
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## Message roots -/

/-- A message whose code is the code at its own target whenever that code is
nonempty and no EIP-7702 designator. -/
def MsgRootCode (msg : Msg) : Prop :=
  ∀ wa, msg.currentTarget = wa → (msg.benv.state.getCode wa).toList ≠ [] →
    ¬ isValidDelegation (msg.benv.state.getCode wa) →
      msg.code = msg.benv.state.getCode wa

/-- A call message that runs its own target's code from its own code address. -/
def MsgOwn (msg : Msg) : Prop :=
  msg.target.isNone = false →
    msg.codeAddress = some msg.currentTarget ∧
      msg.code = msg.benv.state.getCode msg.currentTarget

/-- An actually entered message runs its own target's entry code whenever that
code is nonempty and is not a delegation designator. -/
theorem Frame.enter_run_rootOwnCode {frame : Frame} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {execution : Execution} (run : Exec pc sevm pre execution)
    (enter : frame.enter = .run ⟨pc, sevm, pre⟩) (root : MsgRootCode frame.inner) :
    RootOwnCode ⟨pc, sevm, pre, execution, run⟩ := by
  intro wa target hne hnd
  have hcode : sevm.code = frame.inner.code := Frame.enter_run_code enter
  have htarget : sevm.currentTarget = frame.inner.currentTarget :=
    Frame.enter_run_currentTarget enter
  have hget : ∀ a, pre.getCode a = frame.inner.benv.state.getCode a :=
    Frame.enter_run_getCode enter
  change sevm.currentTarget = wa at target
  change (pre.getCode wa).toList ≠ [] at hne
  change ¬ isValidDelegation (pre.getCode wa) at hnd
  change sevm.code = pre.getCode wa
  rw [hget] at hne hnd ⊢
  rw [hcode]
  exact root wa (htarget ▸ target) hne hnd

theorem RetainedXlot.rawNodes_origin {slot : Xlot} (retained : RetainedXlot slot)
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (hrun : RunFrame frame slot out) (hroot : MsgRootCode frame.inner) :
    OriginList retained.rawNodes := by
  cases retained with
  | none => exact OriginList.nil
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      exact Exec.rawNodes_origin run (Frame.enter_run_rootOwnCode run henter hroot)

theorem ProcessMessageTrace.rawNodes_origin {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (hroot : MsgRootCode msg) :
    OriginList trace.rawNodes :=
  trace.retained.rawNodes_origin trace.run hroot

/-- The actual collision check excludes installed code at a CREATE root's target. -/
theorem processCreateMessage_msg_rootCode {msg : Msg}
    (collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false) :
    MsgRootCode (processCreateMessage.msg msg) := by
  intro wa target hne _
  have hne' : (msg.benv.state.getCode wa).toList ≠ [] := by
    rw [← processCreateMessage.msg_getCode msg wa]
    exact hne
  exact absurd target (ne_wa_of_not_hasCodeOrNonce hne' collision)

theorem ProcessCreateMessageTrace.rawNodes_origin {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false) :
    OriginList trace.rawNodes :=
  trace.retained.rawNodes_origin trace.run (processCreateMessage_msg_rootCode collision)

/-- The EIP-7702 authorization prefix keeps a message running its own target's
code. -/
theorem messageCallDelegation_own {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (target : msg.target.isNone = false) (own : MsgOwn msg) :
    delegated.code = delegated.benv.state.getCode delegated.currentTarget := by
  obtain ⟨address, code⟩ := own target
  have hcur := (messageCallDelegation_fields run).2.2.1
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  by_cases skip : (!msg.benv.stat.rules.delegationEnabled ||
      msg.tenv.stat.auths.isEmpty) = true
  · simp only [skip, ↓reduceIte] at run
    cases run
    exact code
  · simp only [Bool.not_eq_true] at skip
    simp only [skip, Bool.false_eq_true, ↓reduceIte] at run
    obtain ⟨⟨set, counter⟩, hset, hrest⟩ := Except.bind_eq_ok run
    cases hrest
    unfold setDelegation at hset
    obtain ⟨⟨loop, loopRefund⟩, hloop, hafter⟩ := Except.bind_eq_ok hset
    have fields := setDelegationLoop_fields hloop
    have hca : loop.codeAddress = some msg.currentTarget := fields.2.2.2.2.2.trans address
    simp only [hca, Bind.bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at hafter
    obtain ⟨rfl, -⟩ := hafter
    show loop.benv.state.getCode msg.currentTarget = loop.benv.state.getCode loop.currentTarget
    rw [fields.2.2.1]

/-- Code-delegation resolution keeps a message running its own target's code
unless that code is a designator. -/
theorem messageCallExecutionMessage_rootCode {msg : Msg}
    (own : msg.code = msg.benv.state.getCode msg.currentTarget) :
    MsgRootCode (messageCallExecutionMessage msg) := by
  intro wa target hne hnd
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation at target hne hnd ⊢
  split
  · rename_i hnone
    rw [hnone] at target hne hnd
    rw [← target]
    exact own
  · rename_i address hsome
    rw [hsome] at target hnd
    exfalso
    apply hnd
    rw [← target, ← own]
    unfold ForkRules.delegatedCodeAddress at hsome
    split at hsome
    · unfold getDelegatedCodeAddress at hsome
      split at hsome
      · assumption
      · cases hsome
    · cases hsome

theorem MessageCallTrace.rawNodes_origin {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out) (own : MsgOwn msg) :
    OriginList trace.rawNodes := by
  cases trace with
  | createCollision => exact OriginList.nil
  | createRun htarget hcollision evm hcore coreTrace hresult =>
      exact coreTrace.rawNodes_origin (by simpa only [messageCreateCollision] using hcollision)
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm hcore coreTrace
      hresult =>
      subst hexecMsg
      exact coreTrace.rawNodes_origin
        (messageCallExecutionMessage_rootCode (messageCallDelegation_own hdelegation htarget own))

theorem TransactionTrace.rawNodes_origin {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    OriginList trace.rawNodes :=
  trace.message.rawNodes_origin (prepareMessage_own_entry trace.prepared)

theorem ApplyTransactionsTrace.rawNodes_origin {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    OriginList trace.rawNodes := by
  induction trace with
  | nil => exact OriginList.nil
  | cons head tail tailIh => exact OriginList.append head.rawNodes_origin tailIh

theorem SystemMessageTrace.rawNodes_origin {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    OriginList trace.rawNodes :=
  trace.message.rawNodes_origin fun _ => ⟨rfl, rfl⟩

theorem RequestsTrace.rawNodes_origin {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout') :
    OriginList trace.rawNodes :=
  OriginList.append trace.withdrawal.rawNodes_origin trace.consolidation.rawNodes_origin

theorem BeaconStageTrace.rawNodes_origin {rules : ForkRules} {benv : Benv} {state : State}
    {bal : BalBuilder} (trace : BeaconStageTrace rules benv state bal) :
    OriginList trace.rawNodes := by
  cases trace with
  | skipped => exact OriginList.nil
  | called _ _ message _ _ => exact message.rawNodes_origin

theorem HistoryStageTrace.rawNodes_origin {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    OriginList trace.rawNodes := by
  cases trace with
  | skipped => exact OriginList.nil
  | called _ _ _ _ message _ _ => exact message.rawNodes_origin

theorem RequestStageTrace.rawNodes_origin {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    OriginList trace.rawNodes := by
  cases trace with
  | skipped => exact OriginList.nil
  | called _ requests _ => exact requests.rawNodes_origin

theorem StagedBodyTrace.rawNodes_origin {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    OriginList trace.rawNodes :=
  OriginList.append (OriginList.append (OriginList.append trace.beacon.rawNodes_origin
    trace.history.rawNodes_origin) trace.transactions.rawNodes_origin)
    trace.requests.rawNodes_origin

theorem ConfiguredBlockTraceIn.rawNodes_origin {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post) :
    OriginList trace.rawNodes :=
  trace.bodyTrace.rawNodes_origin

/-- **Every raw node of an In-history is reached**: a message root running its
target's own code, a successor of an earlier node of its frame, or the root of a
frame an earlier node spawned. -/
theorem ConfiguredHistoryTraceIn.rawNodes_origin {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    OriginList history.rawNodes := by
  induction history with
  | refl => exact OriginList.nil
  | step prior block ih => exact OriginList.append ih block.rawNodes_origin

end ExecutionTrace

end Blanc
