import Blanc.ExecutionKeptChain
import Blanc.ExecutionTraceEntered

open private TransactionRoots.spine PreparedTx PreparedTx.stat from Blanc.ExecutionKeptChain

/-! Entry-output facts for the actual kept-frame carrier. -/

namespace Blanc

open Jaune ExecutionTrace

/-- Every retained child frame starts with a cleared output buffer. -/
theorem Exec.keptAt_output {a : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    ∀ f ∈ Exec.keptAt a run, f.pre.output = [] := by
  refine Exec.retained_induction
    (P := fun _ _ _ _ run => ∀ f ∈ Exec.keptAt a run, f.pre.output = [])
    ?_ ?_ ?_ ?_ ?_ run committed
  · intro pc sevm pre out step f member
    simp only [Exec.keptAt, List.not_mem_nil] at member
  · intro pc sevm pre pc' post out step next ih f member
    exact ih f (by simpa only [Exec.keptAt] using member)
  · intro pc sevm pre frame resume pc' result post out step enter resumed next ih f member
    exact ih f (by simpa only [Exec.keptAt] using member)
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next settles childIH nextIH
      f member
    rw [Exec.keptAt, dite_eq_left settles, List.mem_append] at member
    rcases member with member | member
    · by_cases here : childEvm.sta.currentTarget = a
      · rw [ite_eq_left here, List.mem_singleton] at member
        subst member
        exact Frame.enter_run_output_empty enter
      · rw [ite_eq_right here] at member
        exact childIH f member
    · exact nextIH f member
  · intro pc sevm pre frame resume pc' childEvm raw post out step enter child resumed next rolled nextIH f member
    rw [Exec.keptAt, dite_eq_right rolled, List.nil_append] at member
    exact nextIH f member

/-- A root with a cleared entry buffer keeps only frames with cleared entry buffers. -/
theorem Root.keptAt_output (r : Root) (empty : r.evm.dyna.output = []) (a : Adr) :
    ∀ f ∈ r.keptAt a, f.pre.output = [] := by
  intro f member
  unfold Root.keptAt at member
  split at member
  next commits =>
    split at member
    next here =>
      rw [List.mem_singleton] at member
      subst member
      exact empty
    next away => exact Exec.keptAt_output r.run (Frame.raw_commits_of_settlementCommits commits) f member
  next rejected => cases member

private theorem enteredFrame_output {frame : Frame} {p : Frame × Evm}
    (entry : enteredFrame frame = some p) : p.2.dyna.output = [] := by
  unfold enteredFrame at entry
  split at entry
  next e entered =>
    cases entry
    exact Frame.enter_run_output_empty entered
  next done result => cases entry

/-- Ordinary top-level entries clear the output buffer. -/
theorem MessageRoots.keptAt_output {msg : Msg} {state : State} {out : MsgCallOutput} {rs : List Root}
    (h : MessageRoots msg state out rs) (neutral : msg.benv.stat.rules.stateGas = none) (a : Adr) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.pre.output = [] := by
  intro f member
  obtain ⟨r, root, member⟩ := List.mem_flatMap.mp member
  apply r.keptAt_output ?_ a f member
  have entry := (h.mem_entry root).1
  simp only [messageEntry, neutral] at entry
  unfold legacyEntry at entry
  split at entry
  · split at entry
    · cases entry
    · exact enteredFrame_output entry
  · split at entry
    · exact enteredFrame_output entry
    · cases entry

/-- Ordinary transaction roots inherit the top-entry output fact. -/
theorem TransactionRoots.keptAt_output {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {sender : Adr} {rs : List Root}
    (h : TransactionRoots benv bout tx index state bout' sender rs)
    (neutral : benv.stat.rules.stateGas = none) (a : Adr) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.pre.output = [] := by
  obtain ⟨msg, messageState, messageOut, refund, tip, facts, roots, _, _⟩ := TransactionRoots.spine h
  apply roots.keptAt_output ?_ a
  rw [PreparedTx.stat facts]
  exact neutral

theorem TransactionsRoots.keptAt_output {txis : List (Nat × Tx)} {benv final : Benv}
    {bout finalOut : BlockOutput} {txs : List (Adr × Tx)} {rs : List Root}
    (h : TransactionsRoots txis benv bout final finalOut txs rs)
    (neutral : benv.stat.rules.stateGas = none) (a : Adr) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.pre.output = [] := by
  induction h with
  | nil => intro f member; cases member
  | cons head tail ih =>
    intro f member
    rw [List.flatMap_append, List.mem_append] at member
    exact member.elim (head.keptAt_output neutral a f) (ih neutral f)

theorem RequestRoots.keptAt_output {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv}
    {acc acc' : List Bytes} {bal bal' : BalBuilder} {final : State} {steps : List RequestStep}
    (h : RequestRoots idx contracts benv acc bal final acc' bal' steps)
    (neutral : benv.stat.rules.stateGas = none) (a : Adr) :
    ∀ f ∈ (requestRootsOf steps).flatMap (Root.keptAt a), f.pre.output = [] := by
  induction h with
  | nil => intro f member; cases member
  | cons call roots tail ih =>
    intro f member
    unfold requestRootsOf at member ih
    rw [List.flatMap_cons, List.flatMap_append, List.mem_append] at member
    exact member.elim (roots.keptAt_output neutral a f) (ih neutral f)

theorem PreCall.keptAt_output {on : Bool} {benv : Benv} {target : Adr} {data : Bytes}
    {st : State} {rs : List Root} (h : PreCall on benv target data st rs)
    (neutral : benv.stat.rules.stateGas = none) (a : Adr) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.pre.output = [] := by
  unfold PreCall at h
  split at h
  · obtain ⟨out, roots⟩ := h
    exact roots.keptAt_output neutral a
  · obtain ⟨_, rfl⟩ := h
    intro f member
    cases member

theorem PreRoots.keptAt_output {benv : Benv} {st : State} {bal : BalBuilder} {rs : List Root}
    (h : PreRoots benv st bal rs) (neutral : benv.stat.rules.stateGas = none) (a : Adr) :
    ∀ f ∈ rs.flatMap (Root.keptAt a), f.pre.output = [] := by
  obtain ⟨beacon, _, beaconRoots, historyRoots, _, first, _, second, rfl⟩ := h
  intro f member
  rw [List.flatMap_append, List.mem_append] at member
  exact member.elim (first.keptAt_output neutral a f) (second.keptAt_output neutral a f)

theorem RequestPass.keptAt_output {benv : Benv} {bout out : BlockOutput} {st : State}
    {steps : List RequestStep} (h : RequestPass benv bout st out steps)
    (neutral : benv.stat.rules.stateGas = none) (a : Adr) :
    ∀ f ∈ (requestRootsOf steps).flatMap (Root.keptAt a), f.pre.output = [] := by
  unfold RequestPass at h
  split at h
  · obtain ⟨deposits, acc, bal, _, roots, _⟩ := h
    exact roots.keptAt_output neutral a
  · obtain ⟨_, _, rfl⟩ := h
    intro f member
    cases member

theorem BodyRoots.keptAt_output {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput} {run : BodyRun}
    (h : BodyRoots benv txs ommers wds state bout run) (neutral : benv.stat.rules.stateGas = none) (a : Adr) :
    ∀ f ∈ run.roots.flatMap (Root.keptAt a), f.pre.output = [] := by
  intro f member
  unfold BodyRun.roots at member
  rw [List.flatMap_append, List.flatMap_append, List.mem_append, List.mem_append] at member
  rcases member with (member | member) | member
  · exact h.pre.keptAt_output neutral a f member
  · obtain ⟨decoded, _, transactions⟩ := h.transactions
    exact transactions.keptAt_output neutral a f member
  · obtain ⟨st, out, requests⟩ := h.requests
    apply requests.keptAt_output ?_ a f member
    change run.txEnv.stat.rules.stateGas = none
    rw [h.txEnv_stat]
    exact neutral

/-- Every frame actually retained by a covered kept history entered with empty output. -/
theorem KeptHistory.keptAt_output {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg start blocks stop) (covered : ∀ b ∈ blocks, CoveredFork b.fork) (a : Adr) :
    ∀ b ∈ blocks, ∀ f ∈ b.keptAt a, f.pre.output = [] := by
  intro b member
  obtain ⟨next, step⟩ := history.mem_step b member
  exact step.body.keptAt_output (CoveredFork.rules_stateGas_none (covered b member)) a

end Blanc
