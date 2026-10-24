import Blanc.ExecutionHistoryCellProvenance

/-!
# Cell provenance from a transaction or block boundary of an In-history

`Blanc/ExecutionHistoryCellProvenance.lean` proves code and cell provenance
relative to the checkpoint. This module restarts it at any committed
boundary inside the history: the start of a block body, or the boundary
after any transaction of a block (`BoundaryAt s pre`, with `s` the world
there and `pre` the raw chronology before it). A boundary never falls inside
a transaction, so its world is committed, the block's `createdAccounts` (empty)
and `stat` hold there, and the existing level lemmas apply verbatim to the
remaining part of the carrier.

Reused (not copied): every `…cellProv_at`/`…cellProv_post` lemma of
`ExecutionHistoryCellProvenance` at the level where the boundary sits, the
`safeRawFrames_of_rawNodes` bridges (`ExecutionInRawNodes`), and
`List.split_append_cons` (`ExecutionAccountingPositional`). The only new
proof steps are the boundary bookkeeping and the writer attribution over a
sublist of the history's chronology.

The checkpoint statement `ConfiguredHistoryTraceIn.rawNode_cellProvenance`
is the instance `boundaryAt_checkpoint`, `pre = []` (see the `example` at the
end).
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-! ## Boundary positions -/

/-- `trace.BoundaryAt s pre`: `pre` is the raw chronology of the transactions
before a transaction boundary of `trace` whose committed world is `s`. -/
def ApplyTransactionsTrace.BoundaryAt :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout →
    State → List Exec.Deriv → Prop
  | _, benv, _, _, _, .nil _ _, s, pre => s = benv.state ∧ pre = []
  | _, benv, _, _, _, .cons head tail, s, pre =>
      (s = benv.state ∧ pre = []) ∨
        ∃ rest, tail.BoundaryAt s rest ∧ pre = head.rawNodes ++ rest

/-- The body start, or a transaction boundary after the beacon and history
system calls. -/
def StagedBodyTrace.BoundaryAt {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (s : State) (pre : List Exec.Deriv) : Prop :=
  (s = benv.state ∧ pre = []) ∨
    ∃ rest, trace.transactions.BoundaryAt s rest ∧
      pre = trace.beacon.rawNodes ++ trace.history.rawNodes ++ rest

/-- A boundary of a configured block is a boundary of its body. -/
def ConfiguredBlockTraceIn.BoundaryAt {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post)
    (s : State) (nodes : List Exec.Deriv) : Prop :=
  trace.bodyTrace.BoundaryAt s nodes

/-- A boundary of a configured history: the checkpoint, or a boundary of one
of its blocks after the raw chronology of the earlier blocks. -/
def ConfiguredHistoryTraceIn.BoundaryAt {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future →
    State → List Exec.Deriv → Prop
  | _, .refl .., s, pre => s = checkpoint.state ∧ pre = []
  | _, .step prior block, s, pre =>
      prior.BoundaryAt s pre ∨ ∃ rest, block.BoundaryAt s rest ∧ pre = prior.rawNodes ++ rest

/-- The checkpoint is a boundary of every history. -/
theorem ConfiguredHistoryTraceIn.boundaryAt_checkpoint
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    history.BoundaryAt checkpoint.state [] := by
  induction history with
  | refl => exact ⟨rfl, rfl⟩
  | step prior block ih => exact Or.inl ih

/-- The remaining transactions after a boundary form a transaction-list
trace from the boundary world with the list's `stat` and `createdAccounts`. -/
theorem ApplyTransactionsTrace.BoundaryAt.suffix
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {s : State} {pre : List Exec.Deriv} (boundary : trace.BoundaryAt s pre) :
    ∃ (txs' : List (Nat × Tx)) (benv' : Benv) (bout' : BlockOutput)
      (tail : ApplyTransactionsTrace txs' benv' bout' finalBenv finalBout),
      benv'.state = s ∧ benv'.stat = benv.stat ∧
        benv'.createdAccounts = benv.createdAccounts ∧
        trace.rawNodes = pre ++ tail.rawNodes := by
  induction trace generalizing pre with
  | nil benv bout =>
      obtain ⟨hs, hpre⟩ := boundary
      exact ⟨_, _, _, .nil benv bout, hs.symm, rfl, rfl, by rw [hpre]; rfl⟩
  | cons head tail ih =>
      rcases boundary with ⟨hs, hpre⟩ | ⟨rest, hb, hpre⟩
      · exact ⟨_, _, _, .cons head tail, hs.symm, rfl, rfl, by rw [hpre]; rfl⟩
      · obtain ⟨txs', benv', bout', tail', hs, hstat, hcr, hnodes⟩ := ih hb
        refine ⟨txs', benv', bout', tail', hs, hstat, hcr, ?_⟩
        simp only [ApplyTransactionsTrace.rawNodes]
        rw [hnodes, hpre, List.append_assoc]

/-- A transaction boundary prefix is a prefix of the list's chronology. -/
theorem ApplyTransactionsTrace.BoundaryAt.prefix
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout}
    {s : State} {pre : List Exec.Deriv} (boundary : trace.BoundaryAt s pre) :
    ∃ rest, trace.rawNodes = pre ++ rest := by
  obtain ⟨_, _, _, tail, -, -, -, hnodes⟩ := boundary.suffix
  exact ⟨tail.rawNodes, hnodes⟩

/-- A body boundary prefix is a prefix of the body's chronology. -/
theorem StagedBodyTrace.BoundaryAt.prefix {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    {trace : StagedBodyTrace benv txs ommers wds state bout}
    {s : State} {pre : List Exec.Deriv} (boundary : trace.BoundaryAt s pre) :
    ∃ rest, trace.rawNodes = pre ++ rest := by
  rcases boundary with ⟨-, hpre⟩ | ⟨rest, hb, hpre⟩
  · exact ⟨trace.rawNodes, by rw [hpre, List.nil_append]⟩
  · obtain ⟨r, hr⟩ := hb.prefix
    refine ⟨r ++ trace.requests.rawNodes, ?_⟩
    simp only [StagedBodyTrace.rawNodes]
    rw [hr, hpre]
    simp only [List.append_assoc]

/-- A block boundary prefix is a prefix of the block's chronology. -/
theorem ConfiguredBlockTraceIn.BoundaryAt.prefix {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} {trace : ConfiguredBlockTraceIn F cfg pre post}
    {s : State} {nodes : List Exec.Deriv} (boundary : trace.BoundaryAt s nodes) :
    ∃ rest, trace.rawNodes = nodes ++ rest :=
  StagedBodyTrace.BoundaryAt.prefix boundary

/-- A boundary prefix is a prefix of the chronology. -/
theorem ConfiguredHistoryTraceIn.BoundaryAt.prefix
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {history : ConfiguredHistoryTraceIn F cfg checkpoint future}
    {s : State} {pre : List Exec.Deriv} (boundary : history.BoundaryAt s pre) :
    ∃ rest, history.rawNodes = pre ++ rest := by
  induction history generalizing pre with
  | refl =>
      obtain ⟨-, hpre⟩ := boundary
      exact ⟨[], by rw [hpre]; rfl⟩
  | step prior block ih =>
      rcases boundary with hb | ⟨rest, hb, hpre⟩
      · obtain ⟨r, hr⟩ := ih hb
        refine ⟨r ++ block.rawNodes, ?_⟩
        simp only [ConfiguredHistoryTraceIn.rawNodes]
        rw [hr, List.append_assoc]
      · obtain ⟨r, hr⟩ := hb.prefix
        refine ⟨r, ?_⟩
        simp only [ConfiguredHistoryTraceIn.rawNodes]
        rw [hr, hpre, List.append_assoc]

/-! ## Transaction lists -/

/-- From a transaction boundary, a transaction list carries the boundary
cell to every later raw node and keeps the boundary code there. -/
theorem ApplyTransactionsTrace.cellProv_at_from {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {s : State} {pre : List Exec.Deriv} (boundary : trace.BoundaryAt s pre)
    (installed : s.getCode wa = C)
    {n : Exec.Deriv} {between after : List Exec.Deriv}
    (hsplit : trace.rawNodes = pre ++ between ++ n :: after)
    (safeBetween : ∀ m ∈ between, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((s.getStor wa).get k) between ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  obtain ⟨_, benv', _, tail, hs, hstat, hcr, hnodes⟩ := boundary.suffix
  rw [hnodes, List.append_assoc] at hsplit
  have htail := List.append_cancel_left hsplit
  subst hs
  exact tail.cellProv_at hCdel k (by rw [hstat]; exact hsg) installed hCne
    (by rw [hcr]; exact hnotCreated) htail rfl safeBetween

/-- From a transaction boundary, a transaction list carries the boundary
cell to its post cell and keeps the boundary code there. -/
theorem ApplyTransactionsTrace.cellProv_post_from {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {s : State} {pre rest : List Exec.Deriv} (boundary : trace.BoundaryAt s pre)
    (installed : s.getCode wa = C)
    (hsplit : trace.rawNodes = pre ++ rest)
    (safeRest : ∀ m ∈ rest, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((s.getStor wa).get k) rest ((finalBenv.state.getStor wa).get k) ∧
      finalBenv.state.getCode wa = C := by
  obtain ⟨_, benv', _, tail, hs, hstat, hcr, hnodes⟩ := boundary.suffix
  rw [hnodes] at hsplit
  have htail := List.append_cancel_left hsplit
  subst hs htail
  exact tail.cellProv_post hCdel k (by rw [hstat]; exact hsg) installed hCne
    (by rw [hcr]; exact hnotCreated) (tail.safeRawFrames_of_rawNodes safeRest)

/-! ## Staged bodies -/

/-- After the transactions, a staged body's withdrawals and requests carry
the transaction-post cell to every request raw node and keep the code. -/
theorem StagedBodyTrace.requests_cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (hcodeT : trace.transactionBenv.state.getCode wa = C)
    {n : Exec.Deriv} {between after : List Exec.Deriv}
    (hsplit : trace.requests.rawNodes = between ++ n :: after)
    (safeBetween : ∀ m ∈ between, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((trace.transactionBenv.state.getStor wa).get k) between
      ((n.devm.getStor wa).get k) ∧ n.devm.getCode wa = C := by
  have txStat : trace.transactionBenv.stat = benv.stat :=
    trace.transactions.stat_eq
  have txCreated : trace.transactionBenv.createdAccounts =
      benv.createdAccounts :=
    trace.transactions.createdAccounts_eq
  have hsgR : (trace.transactionBenv.withState
      trace.withdrawalState).stat.rules.stateGas = Option.none := by
    change trace.transactionBenv.stat.rules.stateGas = Option.none
    rw [txStat]
    exact hsg
  have hnotCreatedR : wa ∉ (trace.transactionBenv.withState
      trace.withdrawalState).createdAccounts := by
    change wa ∉ trace.transactionBenv.createdAccounts
    rw [txCreated]
    exact hnotCreated
  exact trace.requests.cellProv_at hCdel k hsgR
    (trace.withdrawalCode_of_code hcodeT) hCne hnotCreatedR hsplit
    (trace.withdrawalCell_of_code hcodeT hCne k).symm safeBetween

/-- After the transactions, a staged body's withdrawals, requests and
rewards carry the transaction-post cell to the body's post cell and keep
the code. -/
theorem StagedBodyTrace.requests_cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (hcodeT : trace.transactionBenv.state.getCode wa = C)
    (safe : ∀ m ∈ trace.requests.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((trace.transactionBenv.state.getStor wa).get k)
      trace.requests.rawNodes ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  have txStat : trace.transactionBenv.stat = benv.stat :=
    trace.transactions.stat_eq
  have txCreated : trace.transactionBenv.createdAccounts =
      benv.createdAccounts :=
    trace.transactions.createdAccounts_eq
  have hsgR : (trace.transactionBenv.withState
      trace.withdrawalState).stat.rules.stateGas = Option.none := by
    change trace.transactionBenv.stat.rules.stateGas = Option.none
    rw [txStat]
    exact hsg
  have hnotCreatedR : wa ∉ (trace.transactionBenv.withState
      trace.withdrawalState).createdAccounts := by
    change wa ∉ trace.transactionBenv.createdAccounts
    rw [txCreated]
    exact hnotCreated
  obtain ⟨hcellR, hcodeR⟩ := trace.requests.cellProv_post hCdel k hsgR
    (trace.withdrawalCode_of_code hcodeT) hCne hnotCreatedR
    (trace.requests.safeRawFrames_of_rawNodes safe)
  have hcellR' : CellProv wa k ((trace.transactionBenv.state.getStor wa).get k)
      trace.requests.rawNodes ((trace.requestState.getStor wa).get k) := by
    rw [← trace.withdrawalCell_of_code hcodeT hCne k]
    exact hcellR
  have hreward : (trace.rewardState.getStor wa).get k =
      (trace.requestState.getStor wa).get k ∧
      trace.rewardState.getCode wa = C := by
    rw [trace.rewardState_eq]
    split
    · exact ⟨rfl, hcodeR⟩
    · rw [payRewards_getStor _ _ _ _ _ (by rw [hcodeR]; exact hCne),
        payRewards_getCode]
      exact ⟨rfl, hcodeR⟩
  rw [← trace.finalState_eq] at hreward
  rw [hreward.1]
  exact ⟨hcellR', hreward.2⟩

/-- From a body boundary, a staged body carries the boundary cell to every
later raw node and keeps the boundary code there. -/
theorem StagedBodyTrace.cellProv_at_from {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {s : State} {pre : List Exec.Deriv} (boundary : trace.BoundaryAt s pre)
    (installed : s.getCode wa = C)
    {n : Exec.Deriv} {between after : List Exec.Deriv}
    (hsplit : trace.rawNodes = pre ++ between ++ n :: after)
    (safeBetween : ∀ m ∈ between, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((s.getStor wa).get k) between ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  rcases boundary with ⟨hs, hpre⟩ | ⟨rest, hb, hpre⟩
  · subst hs hpre
    rw [List.nil_append] at hsplit
    exact trace.cellProv_at hCdel k hsg installed hCne hnotCreated hsplit rfl
      safeBetween
  · have txStat : ((benv.withState trace.beaconState).withState
        trace.historyState).stat = benv.stat := rfl
    have txCreated : ((benv.withState trace.beaconState).withState
        trace.historyState).createdAccounts = benv.createdAccounts := rfl
    obtain ⟨X, hX⟩ := hb.prefix
    have hrest : X ++ trace.requests.rawNodes = between ++ n :: after := by
      simp only [StagedBodyTrace.rawNodes] at hsplit
      rw [hX, hpre] at hsplit
      simp only [List.append_assoc] at hsplit
      exact List.append_cancel_left (List.append_cancel_left
        (List.append_cancel_left hsplit))
    rcases List.split_append_cons hrest with ⟨m, hXm, -⟩ | ⟨nb, hb', hR⟩
    · rw [hXm, ← List.append_assoc] at hX
      exact trace.transactions.cellProv_at_from hCdel k (by rw [txStat]; exact hsg)
        hCne (by rw [txCreated]; exact hnotCreated) hb installed hX safeBetween
    · obtain ⟨hcellT, hcodeT⟩ := trace.transactions.cellProv_post_from hCdel k
        (by rw [txStat]; exact hsg) hCne (by rw [txCreated]; exact hnotCreated)
        hb installed hX (fun m hm ht =>
          safeBetween m (hb' ▸ List.mem_append_left nb hm) ht)
      obtain ⟨hcellR, hcodeR⟩ := trace.requests_cellProv_at hCdel k hsg hCne
        hnotCreated hcodeT hR (fun m hm ht =>
          safeBetween m (hb' ▸ List.mem_append_right X hm) ht)
      rw [hb']
      exact ⟨CellProv.trans hcellT hcellR, hcodeR⟩

/-- From a body boundary, a staged body carries the boundary cell to its
post cell and keeps the boundary code there. -/
theorem StagedBodyTrace.cellProv_post_from {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {s : State} {pre rest : List Exec.Deriv} (boundary : trace.BoundaryAt s pre)
    (installed : s.getCode wa = C)
    (hsplit : trace.rawNodes = pre ++ rest)
    (safeRest : ∀ m ∈ rest, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((s.getStor wa).get k) rest ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  rcases boundary with ⟨hs, hpre⟩ | ⟨r, hb, hpre⟩
  · subst hs hpre
    rw [List.nil_append] at hsplit
    subst hsplit
    exact trace.cellProv_post hCdel k hsg installed hCne hnotCreated
      (trace.safeRawFrames_of_rawNodes safeRest)
  · have txStat : ((benv.withState trace.beaconState).withState
        trace.historyState).stat = benv.stat := rfl
    have txCreated : ((benv.withState trace.beaconState).withState
        trace.historyState).createdAccounts = benv.createdAccounts := rfl
    obtain ⟨X, hX⟩ := hb.prefix
    have hrest : rest = X ++ trace.requests.rawNodes := by
      simp only [StagedBodyTrace.rawNodes] at hsplit
      rw [hX, hpre] at hsplit
      simp only [List.append_assoc] at hsplit
      exact (List.append_cancel_left (List.append_cancel_left
        (List.append_cancel_left hsplit))).symm
    subst hrest
    obtain ⟨hcellT, hcodeT⟩ := trace.transactions.cellProv_post_from hCdel k
      (by rw [txStat]; exact hsg) hCne (by rw [txCreated]; exact hnotCreated)
      hb installed hX (fun m hm ht =>
        safeRest m (List.mem_append_left _ hm) ht)
    obtain ⟨hcellR, hcodeR⟩ := trace.requests_cellProv_post hCdel k hsg hCne
      hnotCreated hcodeT (fun m hm ht =>
        safeRest m (List.mem_append_right X hm) ht)
    exact ⟨CellProv.trans hcellT hcellR, hcodeR⟩

/-! ## Configured blocks -/

/-- From a block boundary, a configured block carries the boundary cell to
every later raw node and keeps the boundary code there. -/
theorem ConfiguredBlockTraceIn.cellProv_at_from {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) (k : B256)
    {s : State} {nodes : List Exec.Deriv} (boundary : trace.BoundaryAt s nodes)
    (installed : s.getCode wa = C)
    {n : Exec.Deriv} {between after : List Exec.Deriv}
    (hsplit : trace.rawNodes = nodes ++ between ++ n :: after)
    (safeBetween : ∀ m ∈ between, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((s.getStor wa).get k) between ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C :=
  trace.bodyTrace.cellProv_at_from hCdel k
    (capabilities.stateGas_none trace.forkIn) hCne AdrSet.not_mem_empty
    boundary installed hsplit safeBetween

/-- From a block boundary, a configured block carries the boundary cell to
its post cell and keeps the boundary code there. -/
theorem ConfiguredBlockTraceIn.cellProv_post_from {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) (k : B256)
    {s : State} {nodes rest : List Exec.Deriv} (boundary : trace.BoundaryAt s nodes)
    (installed : s.getCode wa = C)
    (hsplit : trace.rawNodes = nodes ++ rest)
    (safeRest : ∀ m ∈ rest, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((s.getStor wa).get k) rest ((post.state.getStor wa).get k) ∧
      post.state.getCode wa = C := by
  have hstate : post.state = trace.bodyState :=
    congrArg BlockChain.state trace.postEq
  rw [hstate]
  exact trace.bodyTrace.cellProv_post_from hCdel k
    (capabilities.stateGas_none trace.forkIn) hCne AdrSet.not_mem_empty
    boundary installed hsplit safeRest

/-! ## Configured histories -/

/-- **Endpoint form from a boundary**: a configured history carries the
boundary cell to its endpoint cell and keeps the boundary code there, from
safety of the raw nodes after the boundary only. -/
theorem ConfiguredHistoryTraceIn.cellProv_post_from
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ []) (k : B256)
    {s : State} {pre rest : List Exec.Deriv} (boundary : history.BoundaryAt s pre)
    (installed : s.getCode wa = C)
    (split : history.rawNodes = pre ++ rest)
    (safeRest : ∀ m ∈ rest, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((s.getStor wa).get k) rest ((future.state.getStor wa).get k) ∧
      future.state.getCode wa = C := by
  induction history generalizing pre rest with
  | refl =>
      obtain ⟨hs, hpre⟩ := boundary
      subst hs hpre
      have hrest : rest = [] := by
        simpa only [ConfiguredHistoryTraceIn.rawNodes, List.nil_append] using split.symm
      subst hrest
      exact ⟨Or.inl rfl, installed⟩
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.rawNodes] at split
      rcases boundary with hb | ⟨r, hb, hpre⟩
      · obtain ⟨r, hr⟩ := hb.prefix
        rw [hr, List.append_assoc] at split
        have hrest := List.append_cancel_left split
        subst hrest
        obtain ⟨hcellP, hcodeP⟩ := ih hb hr (fun m hm ht =>
          safeRest m (List.mem_append_left _ hm) ht)
        obtain ⟨hcellB, hcodeB⟩ := block.cellProv_post hCdel hCne capabilities
          k hcodeP (block.safeRawFrames_of_rawNodes (fun m hm ht =>
            safeRest m (List.mem_append_right r hm) ht))
        exact ⟨CellProv.trans hcellP hcellB, hcodeB⟩
      · rw [hpre, List.append_assoc] at split
        exact block.cellProv_post_from hCdel hCne capabilities k hb installed
          (List.append_cancel_left split) safeRest

/-- From a boundary, a configured history carries the boundary cell to every
later raw node and keeps the boundary code there, from safety of the raw
nodes strictly between the boundary and the node only. -/
theorem ConfiguredHistoryTraceIn.cellProv_at_from {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (k : B256)
    {s : State} {pre : List Exec.Deriv} (boundary : history.BoundaryAt s pre)
    (installed : s.getCode wa = C)
    {n : Exec.Deriv} {between after : List Exec.Deriv}
    (hsplit : history.rawNodes = pre ++ between ++ n :: after)
    (safeBetween : ∀ m ∈ between, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((s.getStor wa).get k) between ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  induction history generalizing pre between n after with
  | refl =>
      obtain ⟨-, hpre⟩ := boundary
      subst hpre
      simp only [ConfiguredHistoryTraceIn.rawNodes] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.rawNodes] at hsplit
      rcases boundary with hb | ⟨r, hb, hpre⟩
      · obtain ⟨r, hr⟩ := hb.prefix
        rw [hr, List.append_assoc, List.append_assoc] at hsplit
        have hrest := List.append_cancel_left hsplit
        rcases List.split_append_cons hrest with ⟨m, hrm, -⟩ | ⟨nb, hbn, hY⟩
        · rw [hrm, ← List.append_assoc] at hr
          exact ih hb hr safeBetween
        · obtain ⟨hcellP, hcodeP⟩ := prior.cellProv_post_from capabilities
            hCdel hCne k hb installed hr (fun m hm ht =>
              safeBetween m (hbn ▸ List.mem_append_left nb hm) ht)
          obtain ⟨hcellB, hcodeB⟩ := block.cellProv_at hCdel hCne capabilities
            k hcodeP hY rfl (fun m hm ht =>
              safeBetween m (hbn ▸ List.mem_append_right r hm) ht)
          rw [hbn]
          exact ⟨CellProv.trans hcellP hcellB, hcodeB⟩
      · rw [hpre, List.append_assoc, List.append_assoc] at hsplit
        have hblock := List.append_cancel_left hsplit
        rw [← List.append_assoc] at hblock
        exact block.cellProv_at_from hCdel hCne capabilities k hb installed
          hblock safeBetween

/-- A provenance witness over a sublist of the history's chronology is a
successful raw `SSTORE` occurrence of one of the history's raw frames. -/
theorem ConfiguredHistoryTraceIn.cellProv_attribution
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {wa : Adr} {k init v : B256} {nodes : List Exec.Deriv}
    (sub : ∀ m ∈ nodes, m ∈ history.rawNodes)
    (cell : CellProv wa k init nodes v) :
    v = init ∨
      ∃ (b₁ b₂ : List Exec.Deriv) (m : Exec.Deriv) (G : Exec.Deriv)
        (write : Exec.SuccessfulSstoreOccurrence G),
        nodes = b₁ ++ m :: b₂ ∧
        G ∈ history.rawFrames ∧
        Exec.Deriv.ParentPrefix G m ∧
        write.occurrence.node = m ∧
        G.sevm.currentTarget = wa ∧
        write.storageOwner = wa ∧ write.key = k ∧
        write.value = v := by
  rcases cell with hinit | ⟨b₁, b₂, m, w, hb, hfound, hown, hkey, hval⟩
  · exact Or.inl hinit
  · right
    have hmemM : m ∈ history.rawNodes :=
      sub m (by rw [hb]; exact List.mem_append_right _ List.mem_cons_self)
    obtain ⟨G, hG, hp⟩ :=
      (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hmemM
    have hmemG : m ∈ Exec.rawNodes G.exc := by
      rcases G with ⟨pc, sevm, pre, out, run⟩
      exact (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run m).mpr
        ⟨_, List.mem_cons_self, hp⟩
    obtain ⟨write, hwrite⟩ :=
      Exec.Deriv.successfulSstore?_sound_raw hmemG hfound
    obtain ⟨hnode, howner⟩ := successfulSstore?_node_owner hfound
    refine ⟨b₁, b₂, m, G, write, hb, hG, hp,
      (congrArg Exec.StorageWrite.node hwrite).trans hnode, ?_, ?_, ?_, ?_⟩
    · rw [← Exec.Deriv.ParentPrefix.sevm_eq hp, ← howner]
      exact hown
    · show write.storageWrite.owner = wa
      rw [hwrite]
      exact hown
    · show write.storageWrite.key = k
      rw [hwrite]
      exact hkey
    · show write.storageWrite.value = _
      rw [hwrite]
      exact hval

/-- **Code and cell provenance from a boundary (G5a′)**. From safety of the
raw nodes strictly between a boundary and a node only, the node sees the
boundary code `C` at `wa`, and its `(wa, k)` cell is the boundary value or the
value of a successful raw `SSTORE` to `(wa, k)` between them, attributed to
its raw frame `G` of the history. -/
theorem ConfiguredHistoryTraceIn.rawNode_cellProvenance_from
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {s : State} {pre : List Exec.Deriv} (boundary : history.BoundaryAt s pre)
    (installed : s.getCode wa = C) (k : B256)
    {between after : List Exec.Deriv} {n : Exec.Deriv}
    (split : history.rawNodes = pre ++ between ++ n :: after)
    (safeBetween : ∀ m ∈ between, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    n.devm.getCode wa = C ∧
      ((Devm.getStor n.devm wa).get k = (s.getStor wa).get k ∨
        ∃ (b₁ b₂ : List Exec.Deriv) (m : Exec.Deriv) (G : Exec.Deriv)
          (write : Exec.SuccessfulSstoreOccurrence G),
          between = b₁ ++ m :: b₂ ∧
          G ∈ history.rawFrames ∧
          Exec.Deriv.ParentPrefix G m ∧
          write.occurrence.node = m ∧
          G.sevm.currentTarget = wa ∧
          write.storageOwner = wa ∧ write.key = k ∧
          write.value = (Devm.getStor n.devm wa).get k) := by
  obtain ⟨hcell, hcode⟩ := history.cellProv_at_from hCdel hCne capabilities k
    boundary installed split safeBetween
  refine ⟨hcode, history.cellProv_attribution (fun m hm => ?_) hcell⟩
  rw [split]
  exact List.mem_append_left _ (List.mem_append_right _ hm)

/-- **Invariant form from a boundary**: a cell property that holds at the
boundary and is preserved by every successful `SSTORE` to `(wa, k)` between
the boundary and the node holds at the node. -/
theorem ConfiguredHistoryTraceIn.rawNode_cellInv_from
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {s : State} {pre : List Exec.Deriv} (boundary : history.BoundaryAt s pre)
    (installed : s.getCode wa = C) {k : B256} {Inv : B256 → Prop}
    (initial : Inv ((s.getStor wa).get k))
    {between after : List Exec.Deriv} {n : Exec.Deriv}
    (split : history.rawNodes = pre ++ between ++ n :: after)
    (safeBetween : ∀ m ∈ between, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct)
    (writesBetween : ∀ m ∈ between, ∀ w : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? m = some w → w.owner = wa → w.key = k → Inv w.value) :
    Inv ((Devm.getStor n.devm wa).get k) := by
  obtain ⟨hcell, -⟩ := history.cellProv_at_from hCdel hCne capabilities k
    boundary installed split safeBetween
  rcases hcell with hinit | ⟨b₁, b₂, m, w, hb, hfound, hown, hkey, hval⟩
  · rw [hinit]
    exact initial
  · rw [← hval]
    exact writesBetween m (by rw [hb]; exact List.mem_append_right _ List.mem_cons_self)
      w hfound hown hkey

/-- **At a raw frame's entry, from a boundary**: the frame root sees the
boundary code and an invariant cell. -/
theorem ConfiguredHistoryTraceIn.rawFrame_entryCellInv_from
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {s : State} {pre : List Exec.Deriv} (boundary : history.BoundaryAt s pre)
    (installed : s.getCode wa = C) {k : B256} {Inv : B256 → Prop}
    (initial : Inv ((s.getStor wa).get k))
    {between after : List Exec.Deriv} {R : Exec.Deriv}
    (member : R ∈ history.rawFrames)
    (split : history.rawNodes = pre ++ between ++ R :: after)
    (safeBetween : ∀ m ∈ between, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct)
    (writesBetween : ∀ m ∈ between, ∀ w : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? m = some w → w.owner = wa → w.key = k → Inv w.value) :
    R.devm.getCode wa = C ∧ Inv ((Devm.getStor R.devm wa).get k) := by
  have _ := member
  exact ⟨(history.cellProv_at_from hCdel hCne capabilities k boundary installed
      split safeBetween).2,
    history.rawNode_cellInv_from capabilities hCdel hCne boundary installed
      initial split safeBetween writesBetween⟩

/-- The checkpoint statement `rawNode_cellProvenance` is the boundary
statement at `boundaryAt_checkpoint`, `pre = []`. -/
example {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    (installed : checkpoint.state.getCode wa = C) (k : B256)
    {before after : List Exec.Deriv} {n : Exec.Deriv}
    (split : history.rawNodes = before ++ n :: after)
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    n.devm.getCode wa = C ∧
      ((Devm.getStor n.devm wa).get k = (checkpoint.state.getStor wa).get k ∨
        ∃ (b₁ b₂ : List Exec.Deriv) (m : Exec.Deriv) (G : Exec.Deriv)
          (write : Exec.SuccessfulSstoreOccurrence G),
          before = b₁ ++ m :: b₂ ∧
          G ∈ history.rawFrames ∧
          Exec.Deriv.ParentPrefix G m ∧
          write.occurrence.node = m ∧
          G.sevm.currentTarget = wa ∧
          write.storageOwner = wa ∧ write.key = k ∧
          write.value = (Devm.getStor n.devm wa).get k) :=
  history.rawNode_cellProvenance_from capabilities hCdel hCne
    history.boundaryAt_checkpoint installed k
    (by rw [List.nil_append]; exact split) safeBefore

end ExecutionTrace

end Blanc
