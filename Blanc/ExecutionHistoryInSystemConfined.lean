import Blanc.ExecutionReceiptLogLink
import Blanc.ExecutionHistoryInCreateAvoid
import Blanc.ExecutionHistoryInSystemOpenings

/-!
# System confinement, from the code at each contract's activation

A system stage's frames stay at the system addresses when each block opens with its fork's canonical
system code, no authorization recovers to a system address, and no CREATE frame lands on one
(`ConfiguredBlockTraceIn.SystemConfined`). Only the first two are inputs: a CREATE frame at a canonical
contract collides (`installedNoFrame_of_opening`). And the openings are not inputs block by block: a
canonical system contract has no self-destruct and cannot be created over, so code once installed
stays (`codeAt_keep_of_cancunOnwards`). What is left is `SystemCodeAtEntries`: each contract's code at
the opening of the first block whose fork installs it. On mainnet that is beacon roots at Cancun's
first block and the other three at Prague's, four `eth_getCode` reads.

* `ConfiguredHistoryTraceIn.SystemConfined`: the code at the entries and the authorizations.
* `ConfiguredHistoryTraceIn.SystemConfined.openings`: every block's opening, from the entries.
* `ConfiguredHistoryTraceIn.SystemConfined.system_ne`: no system frame of the history targets an account
  outside the system addresses.
* `MidHistoryTraceIn.systemConfined_append`: the mid-history form the receipts' laws take.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- What the history's last block's fork installs: nothing for an empty history. -/
def ConfiguredHistoryTraceIn.installedAtTip {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → List (Adr × ByteArray)
  | _, .refl _ _ _ => []
  | _, .step _ block => installedAt block.fork

/-- Each block opens with the canonical code of every contract its fork installs and the previous
block's fork did not. -/
def ConfiguredHistoryTraceIn.SystemCodeAtEntries {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, @ConfiguredHistoryTraceIn.step _ _ _ current _ prior block =>
      prior.SystemCodeAtEntries ∧
        ∀ q ∈ installedAt block.fork, q ∉ prior.installedAtTip → current.state.getCode q.1 = q.2

/-- **A history's system stages are confined:** each system contract has its code when its fork
activates it, and no authorization recovers to a system address. -/
structure ConfiguredHistoryTraceIn.SystemConfined {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    Prop where
  /-- Each system contract has its canonical code at the first block that needs it. -/
  entries : history.SystemCodeAtEntries
  /-- No authorization recovers to a system address. -/
  noAuthority : ∀ p ∈ systemContracts, history.PragueNoAuthorityAt p.1

section Block

variable {cfg : ChainConfig} {pre post : BlockChain}

/-- **Code once installed stays:** a block opening with its fork's system code closes with it. -/
theorem ConfiguredBlockTraceIn.systemCode_keep_of_opening
    (trace : ConfiguredBlockTraceIn HistFork cfg pre post)
    (opening : trace.SystemCodeAtOpening)
    (hauth : ∀ p ∈ systemContracts, trace.PragueNoAuthorityAt p.1) :
    SystemCodeInstalledAt trace.fork post.state := by
  intro q hq
  rcases trace.forkIn.preCancun_cancunOnwards with hpreC | hC
  · rw [HistFork.installedAt_empty_of_preCancun trace.forkIn hpreC] at hq
    simp only [List.not_mem_nil] at hq
  · have hqmem := mem_systemContracts_of_mem_installedAt trace.forkIn hq
    have hqfacts := systemContracts_facts q hqmem
    have hdis : trace.fork.ruleSet.delegationEnabled = false ∨
        ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
          ∀ authority, recoverAuthority auth = .ok authority → authority ≠ q.1 := by
      by_cases hpp : PrePrague trace.fork
      · exact Or.inl (trace.forkIn.delegationDisabled_of_prePrague hpp)
      · exact Or.inr (hauth q hqmem hpp)
    have avoid := trace.createAvoid_of_cancunOnwards BodyStageCapabilities.historical trace.forkIn hC
      hdis (opening q hq) hqfacts.2.2 hqfacts.2.1
    exact trace.codeAt_keep_of_cancunOnwards BodyStageCapabilities.historical trace.forkIn hC hdis
      avoid (opening q hq) hqfacts.2.2 hqfacts.2.1

/-- The block's confinement needs only its opening and its authorizations. -/
theorem ConfiguredBlockTraceIn.systemConfined_of_opening
    (trace : ConfiguredBlockTraceIn HistFork cfg pre post)
    (opening : trace.SystemCodeAtOpening)
    (hauth : ∀ p ∈ systemContracts, trace.PragueNoAuthorityAt p.1) :
    trace.SystemConfined :=
  ⟨opening, hauth, trace.installedNoFrame_of_opening opening hauth⟩

/-- A pre-Cancun block is confined outright. -/
theorem ConfiguredBlockTraceIn.systemConfined_of_preCancun
    (trace : ConfiguredBlockTraceIn HistFork cfg pre post) (hpre : PreCancun trace.fork) :
    trace.SystemConfined :=
  trace.systemConfined_of_opening (SystemCodeInstalledAt.of_preCancun _ trace.forkIn hpre)
    (fun _ _ notPre => (notPre hpre.toPrePrague).elim)

end Block

section History

variable {cfg : ChainConfig} {checkpoint future : BlockChain}

/-- The entries give every block's opening, and the last block's installed set at the end. -/
theorem ConfiguredHistoryTraceIn.openings_of_entries
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (entries : history.SystemCodeAtEntries)
    (hauth : ∀ p ∈ systemContracts, history.PragueNoAuthorityAt p.1) :
    history.SystemCodeAtOpenings ∧ ∀ q ∈ history.installedAtTip, future.state.getCode q.1 = q.2 := by
  induction history with
  | refl => exact ⟨trivial, fun q member => by
      simp only [installedAtTip, List.not_mem_nil] at member⟩
  | step prior block ih =>
    obtain ⟨priorOpenings, priorCode⟩ := ih entries.1 (fun p hp => (hauth p hp).1)
    have opening : block.SystemCodeAtOpening := fun q hq => by
      by_cases carried : q ∈ prior.installedAtTip
      · exact priorCode q carried
      · exact entries.2 q hq carried
    exact ⟨⟨priorOpenings, opening⟩, fun q hq =>
      block.systemCode_keep_of_opening opening (fun p hp => (hauth p hp).2) q hq⟩

/-- **Every block's opening, from the entries.** -/
theorem ConfiguredHistoryTraceIn.SystemConfined.openings
    {history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    (confined : history.SystemConfined) : history.SystemCodeAtOpenings :=
  (history.openings_of_entries confined.entries confined.noAuthority).1

/-- **No system frame of a confined history targets an account outside the system addresses.** -/
theorem ConfiguredHistoryTraceIn.SystemConfined.system_ne
    {history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future}
    (confined : history.SystemConfined) {T : Adr} (notSystem : T ∉ systemTargets) :
    ∀ root ∈ history.systemRawFrames, root.sevm.currentTarget ≠ T := by
  have openings := confined.openings
  have hauth := confined.noAuthority
  clear confined
  induction history with
  | refl => intro root member; simp only [systemRawFrames, List.not_mem_nil] at member
  | step prior block ih =>
    intro root member
    rcases List.mem_append.mp member with early | late
    · exact ih openings.1 (fun p hp => (hauth p hp).1) root early
    · exact block.system_ne block.forkIn
        (block.systemConfined_of_opening openings.2 (fun p hp => (hauth p hp).2)) notSystem root late

/-- A history's gated authorization scopes split across an append. -/
theorem ConfiguredHistoryTraceIn.PragueNoAuthorityAt_append {a b c : BlockChain}
    (left : ConfiguredHistoryTraceIn HistFork cfg a b)
    (right : ConfiguredHistoryTraceIn HistFork cfg b c) (address : Adr) :
    (left.append right).PragueNoAuthorityAt address ↔
      left.PragueNoAuthorityAt address ∧ right.PragueNoAuthorityAt address := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, PragueNoAuthorityAt, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, PragueNoAuthorityAt, ih, and_assoc]

/-- A history's system frames split across an append. -/
theorem ConfiguredHistoryTraceIn.systemRawFrames_append {a b c : BlockChain}
    (left : ConfiguredHistoryTraceIn HistFork cfg a b)
    (right : ConfiguredHistoryTraceIn HistFork cfg b c) :
    (left.append right).systemRawFrames = left.systemRawFrames ++ right.systemRawFrames := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, systemRawFrames, List.append_nil]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, systemRawFrames, ih, List.append_assoc]

/-- A confined history confines any mid history it extends. -/
theorem MidHistoryTraceIn.systemConfined_append {start : Benv} {current : BlockChain}
    (mid : MidHistoryTraceIn HistFork cfg start current) (midConfined : mid.SystemConfined)
    (history : ConfiguredHistoryTraceIn HistFork cfg current future)
    (openings : history.SystemCodeAtOpenings)
    (hauth : ∀ p ∈ systemContracts, history.PragueNoAuthorityAt p.1) :
    (mid.append history).SystemConfined := by
  induction history with
  | refl => exact midConfined
  | step prior block ih =>
    exact ⟨ih openings.1 (fun p hp => (hauth p hp).1),
      block.systemConfined_of_opening openings.2 (fun p hp => (hauth p hp).2)⟩

end History

end Blanc.ExecutionTrace
