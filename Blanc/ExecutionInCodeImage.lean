import Blanc.ExecutionRawFramesCodeImage
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionStagedAdmission
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionTraceSettledForest
import Blanc.Lift.CallerProvenance
import Blanc.StorageOnlySpec

/-!
# Code images and settled positions over In-carrier staged histories

Analogues of `ConfiguredHistoryTrace.rawFrames_codeImage` and
`rawFrames_codeImage_of_installed`
(`Blanc/ExecutionRawFramesCodeImage.lean`), `settled_codeImage`
(`Blanc/ExecutionSettledCodeImage.lean`), `settledFrames_contig` and
`settledFrames_parent` (`Blanc/ExecutionTraceSettledForest.lean`) for the
In-carrier (`StagedBodyTrace` / `ConfiguredBlockTraceIn` /
`ConfiguredHistoryTraceIn`), using the In admission and preservation layer
(`SoundAdmittedIn`, `PreservesAdmittedIn`, `*.stateInv_admitted_semIn`).

The message and transaction levels are fork-free and shared with the modern
carrier, so the existing `MessageCallTrace` / `TransactionTrace` /
`SystemMessageTrace.rawFrames_codeImage` are reused directly; only the levels
that thread the invariant across a fork domain (`ApplyTransactionsTrace`,
`RequestsTrace`, the three stage wrappers, staged bodies, In-blocks and
In-histories) get `…_codeImageIn` versions, each taking the installed
certificate `K` and image identification the In-rungs demand. `of_installed`
variants instantiate the storage-only specification with trivial
preservation. `settled_codeImageIn` follows from the raw-frame version
through the settled-to-raw bridge (`mem_rawFrames_of_mem_settledFrames`);
`settledFrames_contigIn` and `settledFrames_parentIn` follow from the
In-`settledFrames_eq` bridges through the shared `rootFrames_forest`.

Not delivered here: `settled_ownCode` and the ladder-based
`settledFrames_parent_of_codeAddress` need an accounting-ladder runner over
In-histories (the runners only cover `ConfiguredHistoryTrace`) and
fork-domain spawn control (the spawn analysis concludes `CoveredFork`);
neither exists in the In layer.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

open ContractSpecSem

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}

/-- A selected transaction list keeps a code image at every raw frame, under a
selected fork domain. The head runs from the entry invariant (a fork-free
message fact); the tail threads the invariant through the In-rung. -/
theorem ApplyTransactionsTrace.rawFrames_codeImageIn {F : Fork → Prop} {C : ByteArray}
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry) (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      have headInv : c.BenvInv ca (benv.withState txState) :=
        head.benvInv_admitted_semIn preserves hF hsg admitted.1 sumNof inv K image
      have nextSum : sum (benv.withState txState).state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt
          (by simpa only [Benv.withState] using
            processTransaction_sum_le head.result hsg)
          sumNof
      intro root member
      simp only [rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.rawFrames_codeImage inv root member
      · exact ih hF hsg admitted.2 nextSum headInv root member

/-- The two checked request calls keep a code image at every raw frame. -/
theorem RequestsTrace.rawFrames_codeImageIn {F : Fork → Prop} {C : ByteArray}
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  have withdrawal := trace.withdrawal.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.withdrawal inv K image
  have withdrawalInv : c.BenvInv ca (benv.withState trace.withdrawalState) :=
    ⟨withdrawal.1, by simpa only [Benv.withState] using inv.ca⟩
  intro root member
  simp only [rawFrames, List.mem_append] at member
  rcases member with member | member
  · exact trace.withdrawal.rawFrames_codeImage inv root member
  · exact trace.consolidation.rawFrames_codeImage withdrawalInv root member

/-- A beacon stage keeps a code image at every raw frame: skipped stages retain
nothing, a called stage is one fork-free system message. -/
theorem BeaconStageTrace.rawFrames_codeImageIn
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ message _ _ =>
      intro root member
      exact message.rawFrames_codeImage inv root member

/-- A history-storage stage keeps a code image at every raw frame. -/
theorem HistoryStageTrace.rawFrames_codeImageIn
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (inv : c.BenvInv ca benv) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ _ _ message _ _ =>
      intro root member
      exact message.rawFrames_codeImage inv root member

/-- A request stage keeps a code image at every raw frame. -/
theorem RequestStageTrace.rawFrames_codeImageIn {F : Fork → Prop} {C : ByteArray}
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ requests _ =>
      intro root member
      exact requests.rawFrames_codeImageIn preserves hF hsg admitted inv K image root member

/-- A staged body keeps a code image at every raw frame, in D1 stage order.
Stage invariants come back out of the In-rungs; the request entry invariant
is built from the transaction invariant through the (fork-free) withdrawal
pass, exactly as in `StagedBodyTrace.stateInv_admitted_semIn`. -/
theorem StagedBodyTrace.rawFrames_codeImageIn {F : Fork → Prop} {C : ByteArray}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.FrameAdmitted ca entry)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  have beacon := trace.beacon.stateInv_and_sum_le_admitted_semIn
    preserves hF hsg admitted.beacon inv K image
  have beaconInv : c.BenvInv ca (benv.withState trace.beaconState) :=
    ⟨beacon.1, by simpa only [Benv.withState] using inv.ca⟩
  have history := trace.history.stateInv_and_sum_le_admitted_semIn
    preserves (by simpa only [Benv.withState] using hF)
    (by simpa only [Benv.withState] using hsg) admitted.history beaconInv K image
  have historyInv : c.BenvInv ca
      ((benv.withState trace.beaconState).withState trace.historyState) :=
    ⟨history.1, by simpa only [Benv.withState] using beaconInv.ca⟩
  have historySum : sum trace.historyState.bal < 2 ^ 256 := by
    have hle : sum trace.historyState.bal ≤ sum benv.state.bal :=
      le_trans (by simpa only [Benv.withState] using history.2) beacon.2
    omega
  have hFtx : F ((benv.withState trace.beaconState).withState trace.historyState).stat.fork := by
    simpa only [Benv.withState] using hF
  have hsgtx : ((benv.withState trace.beaconState).withState trace.historyState).stat.rules.stateGas = none := by
    simpa only [Benv.withState] using hsg
  have transactionsInv : c.BenvInv ca trace.transactionBenv :=
    trace.transactions.benvInv_admitted_semIn preserves hFtx hsgtx admitted.transactions
      historySum historyInv K image
  have historyLe : sum trace.historyState.bal ≤ sum benv.state.bal :=
    le_trans (by simpa only [Benv.withState] using history.2) beacon.2
  have transactionLe : sum trace.transactionBenv.state.bal ≤ sum benv.state.bal :=
    le_trans (trace.transactions.sum_le_noStateGas (by simpa only [Benv.withState] using hsg))
      historyLe
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have withdrawalInv : c.BenvInv ca (trace.transactionBenv.withState trace.withdrawalState) := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact ⟨transactionsInv.state, by simpa only [Benv.withState] using transactionsInv.ca⟩
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1]
        exact benvInv_processWithdrawalsState_sem transactionsInv (by omega)
  have hFreq : F trace.transactionBenv.stat.fork := by
    rw [txStat]; exact hF
  have hsgreq : trace.transactionBenv.stat.rules.stateGas = none := by
    rw [txStat]; exact hsg
  intro root member
  simp only [rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.rawFrames_codeImageIn inv root member
  · exact trace.history.rawFrames_codeImageIn beaconInv root member
  · exact trace.transactions.rawFrames_codeImageIn preserves hFtx hsgtx admitted.transactions
      historySum historyInv K image root member
  · exact trace.requests.rawFrames_codeImageIn preserves hFreq hsgreq admitted.requests
      withdrawalInv K image root member

/-- A configured In-block keeps a code image at every raw frame: the block
entry invariant plus empty block-level creation, threaded through the body. -/
theorem ConfiguredBlockTraceIn.rawFrames_codeImageIn {F : Fork → Prop} {C : ByteArray}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca pre.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode ca).toList = c.sem.image :=
  trace.bodyTrace.rawFrames_codeImageIn preserves trace.forkIn
    (capabilities.stateGas_none trace.forkIn) admitted trace.withdrawalsBound
    ⟨inv, AdrSet.not_mem_empty⟩ K image

/-- **A certified code image at every raw frame of an In-history**, by refl/step
induction; each block entry invariant comes back out of the prior spine's
In-preservation (reward funding is the explicit premise the rung demands). -/
theorem ConfiguredHistoryTraceIn.rawFrames_codeImageIn {F : Fork → Prop} {C : ByteArray}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : history.FrameAdmitted ca entry)
    (rewards : history.RewardCreditsFunded)
    (inv : c.StateInv ca checkpoint.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    ∀ root ∈ history.rawFrames, some (root.devm.getCode ca).toList = c.sem.image := by
  induction history with
  | refl => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih admitted.1 rewards.1 root member
      · exact block.rawFrames_codeImageIn preserves capabilities admitted.2
          (prior.stateInv_admitted_semIn preserves capabilities admitted.1 rewards.1 inv
            K image)
          K image root member

/-- **A certified code image installed at the checkpoint is at every raw frame**
of the staged body, rolled-back frames included. The storage-only
specification preserves itself trivially. -/
theorem StagedBodyTrace.rawFrames_codeImage_of_installedIn (sem : CodeSem) (a : Adr)
    {F : Fork → Prop} {C : ByteArray}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (inv : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).BenvInv a benv)
    (K : InstalledCert C) (image : sem.image = some C.toList) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode a).toList = sem.image :=
  trace.rawFrames_codeImageIn
    (c := ContractSpecSem.ofStorageOnly sem (fun _ => True)) (ca := a)
    (entry := fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
    hF hsg ((trace.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial)
    bound inv K image

/-- **A certified code image installed at the checkpoint is at every raw frame**
of a configured In-block. -/
theorem ConfiguredBlockTraceIn.rawFrames_codeImage_of_installedIn (sem : CodeSem) (a : Adr)
    {F : Fork → Prop} {C : ByteArray}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (inv : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).StateInv a pre.state)
    (K : InstalledCert C) (image : sem.image = some C.toList) :
    ∀ root ∈ trace.rawFrames, some (root.devm.getCode a).toList = sem.image :=
  trace.rawFrames_codeImageIn
    (c := ContractSpecSem.ofStorageOnly sem (fun _ => True)) (ca := a)
    (entry := fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
    capabilities ((trace.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial)
    inv K image

/-- **A certified code image installed at the checkpoint is at every raw frame**
of a configured In-history, rolled-back frames included. -/
theorem ConfiguredHistoryTraceIn.rawFrames_codeImage_of_installedIn (sem : CodeSem) (a : Adr)
    {F : Fork → Prop} {C : ByteArray}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (rewards : history.RewardCreditsFunded)
    (inv : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).StateInv a checkpoint.state)
    (K : InstalledCert C) (image : sem.image = some C.toList) :
    ∀ root ∈ history.rawFrames, some (root.devm.getCode a).toList = sem.image :=
  history.rawFrames_codeImageIn
    (c := ContractSpecSem.ofStorageOnly sem (fun _ => True)) (ca := a)
    (entry := fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
    capabilities ((history.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial)
    rewards inv K image

/-- **A certified code image stays installed at every settled frame of an
In-history.** Settlement retains only raw roots, so the raw-frame version
applies through the settled-to-raw bridge; the root derivative's world is the
frame's entry world by construction. -/
theorem ConfiguredHistoryTraceIn.settled_codeImageIn (sem : CodeSem) (a : Adr)
    {F : Fork → Prop} {C : ByteArray}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (rewards : history.RewardCreditsFunded)
    (installed : some (checkpoint.state.getCode a).toList = sem.image)
    (K : InstalledCert C) (image : sem.image = some C.toList) :
    ∀ f ∈ history.settledFrames, some (f.pre.getCode a).toList = sem.image := by
  have inv : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).StateInv a checkpoint.state :=
    ⟨installed, trivial, trivial⟩
  have admitted : history.FrameAdmitted a (fun _ _ => True) :=
    (history.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial
  have preserves : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).PreservesAdmittedIn
      F a (fun _ _ => True) := fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩
  have code := history.rawFrames_codeImageIn preserves capabilities admitted rewards inv
    K image
  intro f member
  exact code _ (history.mem_rawFrames_of_mem_settledFrames f member)

/-! ## Settled roots and positions over In-histories -/

/-- The settled message roots of a beacon stage: skipped stages settle nothing. -/
def BeaconStageTrace.settledRoots
    (trace : BeaconStageTrace rules benv state bal) : List Exec.Frame :=
  match trace with
  | .skipped .. => []
  | .called _ _ message _ _ => message.settledRoots

/-- The settled message roots of a history-storage stage. -/
def HistoryStageTrace.settledRoots
    (trace : HistoryStageTrace rules benv inputBal state bal) : List Exec.Frame :=
  match trace with
  | .skipped .. => []
  | .called _ _ _ _ message _ _ => message.settledRoots

/-- The settled message roots of a request stage. -/
def RequestStageTrace.settledRoots
    (trace : RequestStageTrace rules benv bout state bout') : List Exec.Frame :=
  match trace with
  | .skipped .. => []
  | .called _ requests _ => requests.settledRoots

/-- The settled message roots of a staged body, in D1 stage order. -/
def StagedBodyTrace.settledRoots
    (trace : StagedBodyTrace benv txs ommers wds state bout) : List Exec.Frame :=
  trace.beacon.settledRoots ++ trace.history.settledRoots ++
    trace.transactions.settledRoots ++ trace.requests.settledRoots

/-- The settled message roots of a selected-domain block. -/
def ConfiguredBlockTraceIn.settledRoots
    (trace : ConfiguredBlockTraceIn F cfg pre post) : List Exec.Frame :=
  trace.bodyTrace.settledRoots

/-- The settled message roots of a retained history, in execution order. -/
def ConfiguredHistoryTraceIn.settledRoots :
    ConfiguredHistoryTraceIn F cfg checkpoint future → List Exec.Frame
  | .refl _ _ _ => []
  | .step prior block => prior.settledRoots ++ block.settledRoots

theorem BeaconStageTrace.settledFrames_eq
    (trace : BeaconStageTrace rules benv state bal) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  cases trace with
  | skipped => rfl
  | called _ _ message _ _ => exact message.settledFrames_eq

theorem HistoryStageTrace.settledFrames_eq
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  cases trace with
  | skipped => rfl
  | called _ _ _ _ message _ _ => exact message.settledFrames_eq

theorem RequestStageTrace.settledFrames_eq
    (trace : RequestStageTrace rules benv bout state bout') :
    trace.settledFrames = rootFrames trace.settledRoots := by
  cases trace with
  | skipped => rfl
  | called _ requests _ => exact requests.settledFrames_eq

theorem StagedBodyTrace.settledFrames_eq
    (trace : StagedBodyTrace benv txs ommers wds state bout) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  simp only [StagedBodyTrace.settledFrames, StagedBodyTrace.settledRoots, rootFrames,
    List.flatMap_append]
  rw [trace.beacon.settledFrames_eq, trace.history.settledFrames_eq,
    trace.transactions.settledFrames_eq, trace.requests.settledFrames_eq]

theorem ConfiguredBlockTraceIn.settledFrames_eq
    (trace : ConfiguredBlockTraceIn F cfg pre post) :
    trace.settledFrames = rootFrames trace.settledRoots :=
  trace.bodyTrace.settledFrames_eq

theorem ConfiguredHistoryTraceIn.settledFrames_eq
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    history.settledFrames = rootFrames history.settledRoots := by
  induction history with
  | refl => rfl
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.settledFrames, ConfiguredHistoryTraceIn.settledRoots,
        rootFrames, List.flatMap_append]
      rw [ih, block.settledFrames_eq]

/-- **Contiguity of an In-history's settled frames**: at every split, the rest
begins with the selected frame's descendants. -/
theorem ConfiguredHistoryTraceIn.settledFrames_contigIn
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {b : List Exec.Frame} {Fr : Exec.Frame} {a : List Exec.Frame}
    (split : history.settledFrames = b ++ Fr :: a) :
    ∃ r, a = Exec.descendantFrames Fr.run ++ r := by
  rw [history.settledFrames_eq] at split
  exact (rootFrames_forest split).1

/-- **The positional parent of an In-history's settled frame**: it is a settled
message root, or an earlier settled frame `G` spawned it as a direct child and
its position lies inside `G`'s block of descendants. -/
theorem ConfiguredHistoryTraceIn.settledFrames_parentIn
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {b : List Exec.Frame} {Fr : Exec.Frame} {a : List Exec.Frame}
    (split : history.settledFrames = b ++ Fr :: a) :
    Fr ∈ history.settledRoots ∨ ∃ b₁ G b₂, b = b₁ ++ G :: b₂ ∧ Fr ∈ Exec.childFrames G.run ∧
      Exec.SpawnedBy G.sevm Fr ∧ b₂.length < (Exec.descendantFrames G.run).length := by
  rw [history.settledFrames_eq] at split
  exact (rootFrames_forest split).2

end ExecutionTrace

end Blanc
