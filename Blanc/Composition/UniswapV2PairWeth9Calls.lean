import Blanc.Composition.UniswapV2PairWeth9
import Blanc.Lift.UniswapV2Pair.PairCallShape
import Blanc.Composition.Weth9SettledCallers

/-!
# The pair-side input of the WETH9 adapter: what the pair calls at WETH9

`weth9_history_holder_noShrink` takes `HolderCalls p (replayCalls (committedInvocations ca trace))`:
every committed WETH9 writer invocation made by the pair `p` is a `transfer` or a deposit.  This module
derives it from what the Pair code calls:

* `wethHolderSafe_of_selector`: WETH9 decodes a frame whose calldata starts with `transfer` as the
  caller's `transfer`, and one starting with `uniswapV2Call` (no WETH9 selector) as the payable
  fallback, a deposit;
* `holderCalls_of_settled`: `HolderCalls` over the committed invocations follows from that property of
  every settled non-static WETH9 frame whose caller is `p`;
* `pairCalls_holderCalls`: by the generic caller fold (`ConfiguredHistoryTrace.settledFrames_callerTarget_of_children`)
  such a frame is a direct child of a settled Pair frame, so the Pair's call shape
  (`pair_callsTransferOrCallback`) supplies it;
* `weth9_history_holder_noShrink_pairCalls`: the adapter's history theorem with `HolderCalls`
  discharged.

Inputs this tree states but does not discharge are named hypotheses listed after "Conditional on";
this lane's own open obligations are marked `LANE-OPEN`.
-/

namespace Blanc.Composition.UniswapV2PairWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.ExecutionTrace

/-- Whatever WETH9 decodes a frame as, it is a holder call of `p`. -/
def WethHolderSafe (p : Adr) (e : Sevm) : Prop := ∀ c, decodeCall e = some c → HolderCall p c

/-- The decoded call's sender is the frame's caller. -/
theorem callCaller_decodeCall {e : Sevm} {c : Call} (h : decodeCall e = some c) :
    callCaller c = e.caller := by
  unfold decodeCall at h
  split_ifs at h <;> cases h <;> rfl

/-- A frame whose calldata starts with `transfer` or `uniswapV2Call` is, to WETH9, its caller's
`transfer` or a deposit. -/
theorem wethHolderSafe_of_selector {p : Adr} {e : Sevm}
    (sel : Sevm.selector e = 0xa9059cbb ∨ Sevm.selector e = 0x10d1e85c) : WethHolderSafe p e := by
  intro c hc hcaller
  rw [callCaller_decodeCall hc] at hcaller
  subst hcaller
  unfold decodeCall at hc
  by_cases short : shortCall e
  · rw [ite_eq_left short] at hc
    cases hc
    exact Or.inr ⟨e.value, rfl⟩
  rw [ite_eq_right short] at hc
  rcases sel with sel | sel <;> rw [sel] at hc
  · rw [ite_eq_right (by decide), ite_eq_left rfl] at hc
    cases hc
    exact Or.inl ⟨_, _, rfl⟩
  · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_right (by decide)] at hc
    cases hc
    exact Or.inr ⟨e.value, rfl⟩

/-- The fold's property at WETH9: a non-static frame is decoded as a holder call of `p`. -/
def WethQ (p : Adr) (e : Sevm) : Prop := e.isStatic = false → WethHolderSafe p e

/-- **The committed invocations from the settled frames.**  If every settled frame that runs at `ca`
with caller `p` satisfies `WethQ p`, the pair's committed WETH9 writer invocations are transfers or
deposits. -/
theorem holderCalls_of_settled {ca p : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (settled : ∀ F ∈ trace.settledFrames, CallerTarget p ca (WethQ p) F.sevm) :
    HolderCalls p (replayCalls (committedInvocations ca trace)) := by
  intro c hc hcaller
  obtain ⟨inv, hinv, hdec⟩ := List.mem_filterMap.mp hc
  obtain ⟨frame, member, -, target, static, -, rfl⟩ := mem_committedInvocations hinv
  have hcall : frame.sevm.caller = p := (callCaller_decodeCall hdec).symm.trans hcaller
  exact settled frame member target hcall static c hdec hcaller

/-- Named hypothesis, stated but not discharged in this tree: the deployed Pair code stays
installed at `p` over the history, and every settled frame running at `p` runs it from a fresh
pc-zero entry.  Expected source:
the Pair analogue of `weth9_history_committed`'s first conjunct (code intact) together with the raw
frame entry facts (`Exec.rawFrameDescendants_entry`, `Exec.rawFrameDescendants_fresh`), and the Pair
certificate's restriction to CALL/STATICCALL (no DELEGATECALL/CALLCODE puts other code at `p`). -/
def PairFramesRunPairCode (p : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = p →
    G.sevm.code = UniswapV2Pair.code ∧ G.pc = 0 ∧ Exec.FreshEntry G.sevm G.pre ∧
      CoveredFork G.sevm.benvStat.fork

/-- Named hypothesis, stated but not discharged in this tree: the pair never originates a settled
message.  Expected source: `TransactionTrace.sender_ne`
(EIP-3607: a checked sender is never an installed contract), given the Pair code installed at `p` at
each transaction's begin state, and `systemAddress ≠ p` for system messages. -/
def PairSendsNoRootMessage (p : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ p

/-- Named hypothesis, stated but not discharged in this tree: along the chain of every settled
frame running at `p`,
memory stays below `2 ^ 160` bytes.  Expected source: Jaune's per-step potential argument
(`gasMeasure + memcost(memory.size)` never grows along a chain, including over CALL/STATICCALL
spawns; public in 2737c8eb, private at the current pin) with entry gas below `2 ^ 256` (a frame's
entry gas is bounded by its transaction's 256-bit gas limit), via the Jaune reply/memory accounting
export (candidate 2737c8eb) plus a gas bound.  Needed because with unbounded gas the
free-memory pointer can wrap modulo `2 ^ 256` (see `TransferSiteShape`). -/
def CallSiteMemoryBound (p : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = p →
    ChainMemoryBelow ⟨G.pc, G.sevm, G.pre, G.out, G.run⟩ (2 ^ 160)

/-- A direct child of a settled non-static WETH9 frame is called by `ca` itself.  Discharged over the
WETH9 history premises by `weth9_history_settled_children_caller`
(`Blanc/Composition/Weth9SettledCallers.lean`). -/
def Weth9SelfTargetChildren (ca : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = ca → G.sevm.isStatic = false →
    ∀ c ∈ Exec.childFrames G.run, c.sevm.caller = ca

/-- **The pair's WETH9 calls are transfers or deposits, over a configured history.**  The WETH9 side
enters as `Weth9SelfTargetChildren` (proved from the history premises in the headline below).
Conditional on PairFramesRunPairCode, PairSendsNoRootMessage, CallSiteMemoryBound.
LANE-OPEN: conditional on TransferSiteShape, CallbackSiteShape. -/
theorem pairCalls_holderCalls {ca p : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (apart : p ≠ ca)
    (transfer : UniswapV2Pair.TransferSiteShape) (callback : UniswapV2Pair.CallbackSiteShape)
    (pairCode : PairFramesRunPairCode p trace) (noRoot : PairSendsNoRootMessage p trace)
    (memBound : CallSiteMemoryBound p trace)
    (wethSelf : Weth9SelfTargetChildren ca trace) :
    HolderCalls p (replayCalls (committedInvocations ca trace)) := by
  apply holderCalls_of_settled
  have roots : ∀ R ∈ trace.settledRoots, CallerTarget p ca (WethQ p) R.sevm := by
    intro R member _ caller
    exact (noRoot R member caller).elim
  have children : ∀ G ∈ trace.settledFrames,
      CallerChildren p ca (WethQ p) G.sevm (Exec.childFrames G.run) := by
    intro G member which
    rcases which with target | target
    · obtain ⟨codeEq, pcZero, entry, fork⟩ := pairCode G member target
      have bound := memBound G member target
      obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
      dsimp only at codeEq pcZero entry fork bound ⊢
      subst pcZero
      cases out with
      | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
      | ok post =>
          obtain ⟨b, gas, rfl⟩ : ∃ b gas, pre = St b [] Mem.empty gas :=
            ⟨pre, pre.gasLeft, St.self entry.1 entry.2⟩
          have shape := UniswapV2Pair.pair_callsTransferOrCallback transfer callback run
            codeEq fork bound
          intro c hc _ _ static
          exact wethHolderSafe_of_selector (shape c hc static)
    · intro c hc _ caller
      cases static : G.sevm.isStatic
      · rw [wethSelf G member target static c hc] at caller
        exact (apart caller.symm).elim
      · intro nonStatic
        rw [Exec.childFrames_isStatic G.run static c hc] at nonStatic
        cases nonStatic
  exact trace.settledFrames_callerTarget_of_children roots children

/-- **`weth9_history_holder_noShrink` with the pair-side `HolderCalls` discharged.**  As
`weth9_history_holder_noShrink`, with `pairCalls` replaced by what the Pair code calls; the WETH9 side
(`Weth9SelfTargetChildren`) is proved from the same history premises.
Conditional on PairFramesRunPairCode, PairSendsNoRootMessage, CallSiteMemoryBound,
and the `holderTracked`, `allowZero` hypotheses of `weth9_history_holder_noShrink`.
LANE-OPEN: conditional on TransferSiteShape, CallbackSiteShape, EthFits. -/
theorem weth9_history_holder_noShrink_pairCalls {ca p : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace))
    (holderTracked : K₀ (.bal p))
    (allowZero : ∀ g, K₀ (.allow p g) → (checkpoint.state.getStor ca).get (allowSlot p g) = 0)
    (budget : EthFits (checkpoint.state.bal ca).toNat
      (replayCalls (committedInvocations ca trace)))
    (apart : p ≠ ca)
    (transfer : UniswapV2Pair.TransferSiteShape) (callback : UniswapV2Pair.CallbackSiteShape)
    (pairCode : PairFramesRunPairCode p trace) (noRoot : PairSendsNoRootMessage p trace)
    (memBound : CallSiteMemoryBound p trace) :
    ((checkpoint.state.getStor ca).get (balSlot p)).toNat ≤
        ((future.state.getStor ca).get (balSlot p)).toNat +
          holderOut p (replayCalls (committedInvocations ca trace)) ∧
      ∀ g, historyKeyUniverse ca trace K₀ (.allow p g) →
        (future.state.getStor ca).get (allowSlot p g) = 0 :=
  weth9_history_holder_noShrink trace installed sumNof initial fresh holderTracked allowZero
    (pairCalls_holderCalls trace apart transfer callback pairCode noRoot memBound
      (Weth9SettledCallers.weth9_history_settled_children_caller trace installed sumNof initial fresh))
    budget

end Blanc.Composition.UniswapV2PairWeth9
