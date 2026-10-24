import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionStagedBodyTrace
import Blanc.ExecutionHistory
import Blanc.ExecutionOccurrence

/-!
# Raw node chronology of retained In-history traces

Contract-neutral raw-node counterpart of the `rawFrames` chains
(`Blanc/ExecutionTraceFrames.lean`, `Blanc/ExecutionStagedFrames.lean`):
each carrier's `rawNodes` concatenates the same parts with `Exec.rawNodes`
in place of `Exec.rawFrameRoots`. `Exec.rawNodes` lists every reached driver
node in execution order, independently of outcome; the history list is the
true chronology of every executed instruction.

Per level: `mem_rawNodes_iff_rawFrame_parentPrefix` (node membership is
exactly same-frame-or-descendant membership under some listed root, via the
base `Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix`), and
`rawNodes_of_mem_rawFrames` (nodes of a listed root's own run are nodes of
the whole chronology, via `Exec.rawNodes_of_mem_rawFrameRoots`).
`safeRawFrames_of_rawNodes` turns per-node safety into the existing
`SafeRawFrames` premise. `ConfiguredHistoryTraceIn.exists_rawNodes_split_of_mem_rawFrames`
gives the positional split of a listed root.

Reused (not copied): `Exec.rawNodes_of_mem_rawFrameRoots`,
`Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix`,
`ExecutionTrace.SafeRawFrames` and its `append`/`of_append` transport.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- A same-frame-or-descendant node of a derivation is one of its raw nodes.
Inline of the one-line `Exec.mem_rawNodes_of_parentPrefix_root` glue
(`Blanc/SourceAttainment.lean`): the root is its own raw frame root. -/
private theorem mem_rawNodes_of_parentPrefix_deriv {R node : Exec.Deriv}
    (h : Exec.Deriv.ParentPrefix R node) : node ∈ Exec.rawNodes R.exc := by
  obtain ⟨pc, sevm, pre, out, run⟩ := R
  exact (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run node).mpr
    ⟨_, List.mem_cons_self, h⟩

def RetainedXlot.rawNodes {slot : Xlot} : RetainedXlot slot → List Exec.Deriv
  | .none => []
  | .some run => Exec.rawNodes run

theorem RetainedXlot.mem_rawNodes_iff_rawFrame_parentPrefix
    {slot : Xlot} (trace : RetainedXlot slot) (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  cases trace with
  | none =>
      simp only [RetainedXlot.rawNodes, RetainedXlot.rawFrames,
        List.not_mem_nil, false_and, exists_false]
  | some run =>
      simp only [RetainedXlot.rawNodes, RetainedXlot.rawFrames]
      exact Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run node

theorem RetainedXlot.rawNodes_of_mem_rawFrames {slot : Xlot}
    (trace : RetainedXlot slot) (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  cases trace with
  | none =>
      simp only [RetainedXlot.rawFrames, List.not_mem_nil] at hR
  | some run =>
      simp only [RetainedXlot.rawFrames] at hR
      simp only [RetainedXlot.rawNodes]
      exact Exec.rawNodes_of_mem_rawFrameRoots run R hR node hn

theorem RetainedXlot.safeRawFrames_of_rawNodes {slot : Xlot} {wa : Adr}
    (trace : RetainedXlot slot)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def ProcessMessageTrace.rawNodes {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) : List Exec.Deriv :=
  trace.retained.rawNodes

theorem ProcessMessageTrace.mem_rawNodes_iff_rawFrame_parentPrefix {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  simp only [ProcessMessageTrace.rawNodes, ProcessMessageTrace.rawFrames]
  exact trace.retained.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem ProcessMessageTrace.rawNodes_of_mem_rawFrames {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  simp only [ProcessMessageTrace.rawFrames] at hR
  simp only [ProcessMessageTrace.rawNodes]
  exact trace.retained.rawNodes_of_mem_rawFrames R hR node hn

theorem ProcessMessageTrace.safeRawFrames_of_rawNodes {wa : Adr} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def ProcessCreateMessageTrace.rawNodes {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) : List Exec.Deriv :=
  trace.retained.rawNodes

theorem ProcessCreateMessageTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  simp only [ProcessCreateMessageTrace.rawNodes,
    ProcessCreateMessageTrace.rawFrames]
  exact trace.retained.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem ProcessCreateMessageTrace.rawNodes_of_mem_rawFrames {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  simp only [ProcessCreateMessageTrace.rawFrames] at hR
  simp only [ProcessCreateMessageTrace.rawNodes]
  exact trace.retained.rawNodes_of_mem_rawFrames R hR node hn

theorem ProcessCreateMessageTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def MessageCallTrace.rawNodes :
    MessageCallTrace msg state out → List Exec.Deriv
  | .createCollision .. => []
  | .createRun _ _ _ _ core _ => core.rawNodes
  | .callRun _ _ _ _ _ _ _ _ core _ => core.rawNodes

theorem MessageCallTrace.mem_rawNodes_iff_rawFrame_parentPrefix {msg : Msg}
    {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  cases trace with
  | createCollision =>
      simp only [MessageCallTrace.rawNodes, MessageCallTrace.rawFrames,
        List.not_mem_nil, false_and, exists_false]
  | createRun target collision evm core coreTrace result =>
      simp only [MessageCallTrace.rawNodes, MessageCallTrace.rawFrames]
      exact coreTrace.mem_rawNodes_iff_rawFrame_parentPrefix node
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      simp only [MessageCallTrace.rawNodes, MessageCallTrace.rawFrames]
      exact coreTrace.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem MessageCallTrace.rawNodes_of_mem_rawFrames {msg : Msg}
    {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  cases trace with
  | createCollision =>
      simp only [MessageCallTrace.rawFrames, List.not_mem_nil] at hR
  | createRun target collision evm core coreTrace result =>
      simp only [MessageCallTrace.rawFrames] at hR
      simp only [MessageCallTrace.rawNodes]
      exact coreTrace.rawNodes_of_mem_rawFrames R hR node hn
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      simp only [MessageCallTrace.rawFrames] at hR
      simp only [MessageCallTrace.rawNodes]
      exact coreTrace.rawNodes_of_mem_rawFrames R hR node hn

theorem MessageCallTrace.safeRawFrames_of_rawNodes {wa : Adr} {msg : Msg}
    {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def TransactionTrace.rawNodes {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    List Exec.Deriv :=
  trace.message.rawNodes

theorem TransactionTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  simp only [TransactionTrace.rawNodes, TransactionTrace.rawFrames]
  exact trace.message.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem TransactionTrace.rawNodes_of_mem_rawFrames
    {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  simp only [TransactionTrace.rawFrames] at hR
  simp only [TransactionTrace.rawNodes]
  exact trace.message.rawNodes_of_mem_rawFrames R hR node hn

theorem TransactionTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def ApplyTransactionsTrace.rawNodes :
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → List Exec.Deriv
  | .nil _ _ => []
  | .cons head tail => head.rawNodes ++ tail.rawNodes

theorem ApplyTransactionsTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  induction trace with
  | nil =>
      simp only [ApplyTransactionsTrace.rawNodes,
        ApplyTransactionsTrace.rawFrames, List.not_mem_nil, false_and,
        exists_false]
  | cons head tail tailIh =>
      simp only [ApplyTransactionsTrace.rawNodes,
        ApplyTransactionsTrace.rawFrames, List.mem_append]
      constructor
      · rintro (h | h)
        · obtain ⟨R, hR, hp⟩ :=
            (head.mem_rawNodes_iff_rawFrame_parentPrefix node).mp h
          exact ⟨R, Or.inl hR, hp⟩
        · obtain ⟨R, hR, hp⟩ := tailIh.mp h
          exact ⟨R, Or.inr hR, hp⟩
      · rintro ⟨R, hR | hR, hp⟩
        · exact Or.inl
            ((head.mem_rawNodes_iff_rawFrame_parentPrefix node).mpr
              ⟨R, hR, hp⟩)
        · exact Or.inr (tailIh.mpr ⟨R, hR, hp⟩)

theorem ApplyTransactionsTrace.rawNodes_of_mem_rawFrames
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  induction trace with
  | nil =>
      simp only [ApplyTransactionsTrace.rawFrames,
        List.not_mem_nil] at hR
  | cons head tail tailIh =>
      simp only [ApplyTransactionsTrace.rawFrames,
        List.mem_append] at hR
      simp only [ApplyTransactionsTrace.rawNodes, List.mem_append]
      rcases hR with h | h
      · exact Or.inl (head.rawNodes_of_mem_rawFrames R h node hn)
      · exact Or.inr (tailIh h)

theorem ApplyTransactionsTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def SystemMessageTrace.rawNodes {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) :
    List Exec.Deriv :=
  trace.message.rawNodes

theorem SystemMessageTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  simp only [SystemMessageTrace.rawNodes, SystemMessageTrace.rawFrames]
  exact trace.message.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem SystemMessageTrace.rawNodes_of_mem_rawFrames
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  simp only [SystemMessageTrace.rawFrames] at hR
  simp only [SystemMessageTrace.rawNodes]
  exact trace.message.rawNodes_of_mem_rawFrames R hR node hn

theorem SystemMessageTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def RequestsTrace.rawNodes {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') : List Exec.Deriv :=
  trace.withdrawal.rawNodes ++ trace.consolidation.rawNodes

theorem RequestsTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  simp only [RequestsTrace.rawNodes, RequestsTrace.rawFrames,
    List.mem_append]
  constructor
  · rintro (h | h)
    · obtain ⟨R, hR, hp⟩ :=
        (trace.withdrawal.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mp h
      exact ⟨R, Or.inl hR, hp⟩
    · obtain ⟨R, hR, hp⟩ :=
        (trace.consolidation.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mp h
      exact ⟨R, Or.inr hR, hp⟩
  · rintro ⟨R, hR | hR, hp⟩
    · exact Or.inl
        ((trace.withdrawal.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mpr ⟨R, hR, hp⟩)
    · exact Or.inr
        ((trace.consolidation.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mpr ⟨R, hR, hp⟩)

theorem RequestsTrace.rawNodes_of_mem_rawFrames
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  simp only [RequestsTrace.rawFrames, List.mem_append] at hR
  simp only [RequestsTrace.rawNodes, List.mem_append]
  rcases hR with h | h
  · exact Or.inl (trace.withdrawal.rawNodes_of_mem_rawFrames R h node hn)
  · exact Or.inr (trace.consolidation.rawNodes_of_mem_rawFrames R h node hn)

theorem RequestsTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def BeaconStageTrace.rawNodes {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder}
    : BeaconStageTrace rules benv state bal → List Exec.Deriv
  | .skipped .. => []
  | .called _ _ message _ _ => message.rawNodes

theorem BeaconStageTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  cases trace with
  | skipped =>
      simp only [BeaconStageTrace.rawNodes, BeaconStageTrace.rawFrames,
        List.not_mem_nil, false_and, exists_false]
  | called enabled out message incorporated run =>
      simp only [BeaconStageTrace.rawNodes, BeaconStageTrace.rawFrames]
      exact message.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem BeaconStageTrace.rawNodes_of_mem_rawFrames
    {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  cases trace with
  | skipped =>
      simp only [BeaconStageTrace.rawFrames, List.not_mem_nil] at hR
  | called enabled out message incorporated run =>
      simp only [BeaconStageTrace.rawFrames] at hR
      simp only [BeaconStageTrace.rawNodes]
      exact message.rawNodes_of_mem_rawFrames R hR node hn

theorem BeaconStageTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {rules : ForkRules} {benv : Benv}
    {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def HistoryStageTrace.rawNodes {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    : HistoryStageTrace rules benv inputBal state bal → List Exec.Deriv
  | .skipped .. => []
  | .called _ _ _ _ message _ _ => message.rawNodes

theorem HistoryStageTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  cases trace with
  | skipped =>
      simp only [HistoryStageTrace.rawNodes, HistoryStageTrace.rawFrames,
        List.not_mem_nil, false_and, exists_false]
  | called enabled lastHash lastHashRun out message incorporated run =>
      simp only [HistoryStageTrace.rawNodes, HistoryStageTrace.rawFrames]
      exact message.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem HistoryStageTrace.rawNodes_of_mem_rawFrames
    {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  cases trace with
  | skipped =>
      simp only [HistoryStageTrace.rawFrames, List.not_mem_nil] at hR
  | called enabled lastHash lastHashRun out message incorporated run =>
      simp only [HistoryStageTrace.rawFrames] at hR
      simp only [HistoryStageTrace.rawNodes]
      exact message.rawNodes_of_mem_rawFrames R hR node hn

theorem HistoryStageTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {rules : ForkRules} {benv : Benv}
    {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def RequestStageTrace.rawNodes {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    : RequestStageTrace rules benv bout state bout' → List Exec.Deriv
  | .skipped .. => []
  | .called _ requests _ => requests.rawNodes

theorem RequestStageTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  cases trace with
  | skipped =>
      simp only [RequestStageTrace.rawNodes, RequestStageTrace.rawFrames,
        List.not_mem_nil, false_and, exists_false]
  | called enabled requests run =>
      simp only [RequestStageTrace.rawNodes, RequestStageTrace.rawFrames]
      exact requests.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem RequestStageTrace.rawNodes_of_mem_rawFrames
    {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  cases trace with
  | skipped =>
      simp only [RequestStageTrace.rawFrames, List.not_mem_nil] at hR
  | called enabled requests run =>
      simp only [RequestStageTrace.rawFrames] at hR
      simp only [RequestStageTrace.rawNodes]
      exact requests.rawNodes_of_mem_rawFrames R hR node hn

theorem RequestStageTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def StagedBodyTrace.rawNodes {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    List Exec.Deriv :=
  trace.beacon.rawNodes ++ trace.history.rawNodes ++
    trace.transactions.rawNodes ++ trace.requests.rawNodes

theorem StagedBodyTrace.mem_rawNodes_iff_rawFrame_parentPrefix
    {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  simp only [StagedBodyTrace.rawNodes, StagedBodyTrace.rawFrames,
    List.mem_append]
  constructor
  · rintro (((h | h) | h) | h)
    · obtain ⟨R, hR, hp⟩ :=
        (trace.beacon.mem_rawNodes_iff_rawFrame_parentPrefix node).mp h
      exact ⟨R, Or.inl (Or.inl (Or.inl hR)), hp⟩
    · obtain ⟨R, hR, hp⟩ :=
        (trace.history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp h
      exact ⟨R, Or.inl (Or.inl (Or.inr hR)), hp⟩
    · obtain ⟨R, hR, hp⟩ :=
        (trace.transactions.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mp h
      exact ⟨R, Or.inl (Or.inr hR), hp⟩
    · obtain ⟨R, hR, hp⟩ :=
        (trace.requests.mem_rawNodes_iff_rawFrame_parentPrefix node).mp h
      exact ⟨R, Or.inr hR, hp⟩
  · rintro ⟨R, ((hR | hR) | hR) | hR, hp⟩
    · exact Or.inl (Or.inl (Or.inl
        ((trace.beacon.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mpr ⟨R, hR, hp⟩)))
    · exact Or.inl (Or.inl (Or.inr
        ((trace.history.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mpr ⟨R, hR, hp⟩)))
    · exact Or.inl (Or.inr
        ((trace.transactions.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mpr ⟨R, hR, hp⟩))
    · exact Or.inr
        ((trace.requests.mem_rawNodes_iff_rawFrame_parentPrefix
          node).mpr ⟨R, hR, hp⟩)

theorem StagedBodyTrace.rawNodes_of_mem_rawFrames
    {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  simp only [StagedBodyTrace.rawFrames, List.mem_append] at hR
  simp only [StagedBodyTrace.rawNodes, List.mem_append]
  rcases hR with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl
      (trace.beacon.rawNodes_of_mem_rawFrames R h node hn)))
  · exact Or.inl (Or.inl (Or.inr
      (trace.history.rawNodes_of_mem_rawFrames R h node hn)))
  · exact Or.inl (Or.inr
      (trace.transactions.rawNodes_of_mem_rawFrames R h node hn))
  · exact Or.inr (trace.requests.rawNodes_of_mem_rawFrames R h node hn)

theorem StagedBodyTrace.safeRawFrames_of_rawNodes {wa : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def ConfiguredBlockTraceIn.rawNodes {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) : List Exec.Deriv :=
  trace.bodyTrace.rawNodes

theorem ConfiguredBlockTraceIn.mem_rawNodes_iff_rawFrame_parentPrefix
    {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) (node : Exec.Deriv) :
    node ∈ trace.rawNodes ↔
      ∃ R ∈ trace.rawFrames, Exec.Deriv.ParentPrefix R node := by
  simp only [ConfiguredBlockTraceIn.rawNodes,
    ConfiguredBlockTraceIn.rawFrames]
  exact trace.bodyTrace.mem_rawNodes_iff_rawFrame_parentPrefix node

theorem ConfiguredBlockTraceIn.rawNodes_of_mem_rawFrames
    {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) (R : Exec.Deriv)
    (hR : R ∈ trace.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ trace.rawNodes := by
  simp only [ConfiguredBlockTraceIn.rawFrames] at hR
  simp only [ConfiguredBlockTraceIn.rawNodes]
  exact trace.bodyTrace.rawNodes_of_mem_rawFrames R hR node hn

theorem ConfiguredBlockTraceIn.safeRawFrames_of_rawNodes {wa : Adr}
    {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (h : ∀ m ∈ trace.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa trace.rawFrames := by
  intro R hR node hn ht
  exact h node (trace.rawNodes_of_mem_rawFrames R hR node hn) ht

def ConfiguredHistoryTraceIn.rawNodes {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} →
    ConfiguredHistoryTraceIn F cfg checkpoint future → List Exec.Deriv
  | _, .refl .. => []
  | _, .step prior block => prior.rawNodes ++ block.rawNodes

theorem ConfiguredHistoryTraceIn.mem_rawNodes_iff_rawFrame_parentPrefix
    {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (node : Exec.Deriv) :
    node ∈ history.rawNodes ↔
      ∃ R ∈ history.rawFrames, Exec.Deriv.ParentPrefix R node := by
  cases history with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.rawNodes,
        ConfiguredHistoryTraceIn.rawFrames, List.not_mem_nil, false_and,
        exists_false]
  | step prior block =>
      simp only [ConfiguredHistoryTraceIn.rawNodes,
        ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
      constructor
      · rintro (h | h)
        · obtain ⟨R, hR, hp⟩ :=
            (prior.mem_rawNodes_iff_rawFrame_parentPrefix node).mp h
          exact ⟨R, Or.inl hR, hp⟩
        · obtain ⟨R, hR, hp⟩ :=
            (block.mem_rawNodes_iff_rawFrame_parentPrefix node).mp h
          exact ⟨R, Or.inr hR, hp⟩
      · rintro ⟨R, hR | hR, hp⟩
        · exact Or.inl
            ((prior.mem_rawNodes_iff_rawFrame_parentPrefix node).mpr
              ⟨R, hR, hp⟩)
        · exact Or.inr
            ((block.mem_rawNodes_iff_rawFrame_parentPrefix node).mpr
              ⟨R, hR, hp⟩)

theorem ConfiguredHistoryTraceIn.rawNodes_of_mem_rawFrames
    {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (R : Exec.Deriv)
    (hR : R ∈ history.rawFrames) (node : Exec.Deriv)
    (hn : node ∈ Exec.rawNodes R.exc) : node ∈ history.rawNodes := by
  cases history with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.rawFrames,
        List.not_mem_nil] at hR
  | step prior block =>
      simp only [ConfiguredHistoryTraceIn.rawFrames,
        List.mem_append] at hR
      simp only [ConfiguredHistoryTraceIn.rawNodes, List.mem_append]
      rcases hR with h | h
      · exact Or.inl (prior.rawNodes_of_mem_rawFrames R h node hn)
      · exact Or.inr (block.rawNodes_of_mem_rawFrames R h node hn)

theorem ConfiguredHistoryTraceIn.safeRawFrames_of_rawNodes {wa : Adr}
    {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (h : ∀ m ∈ history.rawNodes, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    SafeRawFrames wa history.rawFrames := by
  intro R hR node hn ht
  exact h node (history.rawNodes_of_mem_rawFrames R hR node hn) ht

/-- Every raw frame root is a raw node: `ParentPrefix.refl` through the
bridge, positionally. Values can repeat, so the split is positional. -/
theorem ConfiguredHistoryTraceIn.exists_rawNodes_split_of_mem_rawFrames
    {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {R : Exec.Deriv} (member : R ∈ history.rawFrames) :
    ∃ before after, history.rawNodes = before ++ R :: after := by
  have hR : R ∈ history.rawNodes :=
    history.rawNodes_of_mem_rawFrames R member R
      (mem_rawNodes_of_parentPrefix_deriv (.refl R))
  exact List.append_of_mem hR

end ExecutionTrace

end Blanc
