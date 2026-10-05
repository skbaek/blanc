import Blanc.Composition.UniswapV2PairWeth9
import Blanc.Lift.UniswapV2Pair.PairCallShape

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
* `pairCalls_holderCalls`: by the generic caller fold (`ConfiguredHistoryTrace.settledFrames_callerTarget`)
  such a frame is a direct child of a settled Pair frame, so the Pair's call shape
  (`pair_callsTransferOrCallback`) supplies it;
* `weth9_history_holder_noShrink_pairCalls`: the adapter's history theorem with `HolderCalls`
  discharged.

The cross-host inputs are named hypotheses marked `CROSS-HOST`.
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

/-- CROSS-HOST HYPOTHESIS (delete at consolidation): discharged by the original host's Pair history
replay (handoff "Original-host deliverables" 2): the deployed Pair code stays installed at `p` over the
history, and every settled frame running at `p` runs it from a fresh pc-zero entry.  Expected source:
the Pair analogue of `weth9_history_committed`'s first conjunct (code intact) together with the raw
frame entry facts (`Exec.rawFrameDescendants_entry`, `Exec.rawFrameDescendants_fresh`), and the Pair
certificate's restriction to CALL/STATICCALL (no DELEGATECALL/CALLCODE puts other code at `p`). -/
def PairFramesRunPairCode (p : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = p →
    G.sevm.code = UniswapV2Pair.code ∧ G.pc = 0 ∧ Exec.FreshEntry G.sevm G.pre ∧
      CoveredFork G.sevm.benvStat.fork

/-- CROSS-HOST HYPOTHESIS (delete at consolidation): discharged by the original host's Pair history
replay: the pair never originates a settled message.  Expected source: `TransactionTrace.sender_ne`
(EIP-3607: a checked sender is never an installed contract), given the Pair code installed at `p` at
each transaction's begin state, and `systemAddress ≠ p` for system messages. -/
def PairSendsNoRootMessage (p : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ p

/-- CROSS-HOST HYPOTHESIS (delete at consolidation): discharged by new-host (this lane's) WETH9-side
work: a direct child of a settled WETH9 frame that stays at `ca` is called by `ca` itself.  Expected
source: the WETH9 certificate executes no external instruction but the `withdraw` CALL
(`SFunc.execsSatisfy`, as in `Blanc/Lift/StaticOnlyFrames.lean`), a CALL spawn hands the current
target as caller, and every settled frame at `ca` runs the WETH9 code (the accounting ladder's
`CodeSem.At` invariant behind `weth9_history_committed`, which is not exported per frame). -/
def Weth9SelfTargetChildren (ca : Adr) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = ca →
    ∀ c ∈ Exec.childFrames G.run, c.sevm.currentTarget = ca → c.sevm.caller = ca

/-- **The pair's WETH9 calls are transfers or deposits, over a configured history.**
CROSS-HOST: conditional on QuietEntriesCallShape, SkimCallShape, SwapCallShape, BurnCallShape,
PairFramesRunPairCode, PairSendsNoRootMessage, Weth9SelfTargetChildren. -/
theorem pairCalls_holderCalls {ca p : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (apart : p ≠ ca)
    (quiet : UniswapV2Pair.QuietEntriesCallShape) (skim : UniswapV2Pair.SkimCallShape)
    (swap : UniswapV2Pair.SwapCallShape) (burn : UniswapV2Pair.BurnCallShape)
    (pairCode : PairFramesRunPairCode p trace) (noRoot : PairSendsNoRootMessage p trace)
    (wethSelf : Weth9SelfTargetChildren ca trace) :
    HolderCalls p (replayCalls (committedInvocations ca trace)) := by
  apply holderCalls_of_settled
  have roots : ∀ R ∈ trace.settledRoots, CallerTarget p ca (WethQ p) R.sevm := by
    intro R member _ caller
    exact (noRoot R member caller).elim
  have issuers : ∀ G ∈ trace.settledFrames,
      CallerIssuers p ca (WethQ p) G.sevm (Exec.childFrames G.run) := by
    intro G member
    refine ⟨fun target => ?_, fun target c hc ctarget => ?_⟩
    · obtain ⟨codeEq, pcZero, entry, fork⟩ := pairCode G member target
      obtain ⟨pc, sevm, pre, out, run, committed⟩ := G
      dsimp only at codeEq pcZero entry fork ⊢
      subst pcZero
      cases out with
      | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
      | ok post =>
          obtain ⟨b, gas, rfl⟩ : ∃ b gas, pre = St b [] Mem.empty gas :=
            ⟨pre, pre.gasLeft, St.self entry.1 entry.2⟩
          have shape := UniswapV2Pair.pair_callsTransferOrCallback quiet skim swap burn run
            codeEq fork
          intro c hc _ _ static
          exact wethHolderSafe_of_selector (shape c hc static)
    · rw [wethSelf G member target c hc ctarget]
      exact fun same => apart same.symm
  exact trace.settledFrames_callerTarget roots issuers

/-- **`weth9_history_holder_noShrink` with the pair-side `HolderCalls` discharged.**  As
`weth9_history_holder_noShrink`, with `pairCalls` replaced by what the Pair code calls.
CROSS-HOST: conditional on QuietEntriesCallShape, SkimCallShape, SwapCallShape, BurnCallShape,
PairFramesRunPairCode, PairSendsNoRootMessage, Weth9SelfTargetChildren. -/
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
    (quiet : UniswapV2Pair.QuietEntriesCallShape) (skim : UniswapV2Pair.SkimCallShape)
    (swap : UniswapV2Pair.SwapCallShape) (burn : UniswapV2Pair.BurnCallShape)
    (pairCode : PairFramesRunPairCode p trace) (noRoot : PairSendsNoRootMessage p trace)
    (wethSelf : Weth9SelfTargetChildren ca trace) :
    ((checkpoint.state.getStor ca).get (balSlot p)).toNat ≤
        ((future.state.getStor ca).get (balSlot p)).toNat +
          holderOut p (replayCalls (committedInvocations ca trace)) ∧
      ∀ g, historyKeyUniverse ca trace K₀ (.allow p g) →
        (future.state.getStor ca).get (allowSlot p g) = 0 :=
  weth9_history_holder_noShrink trace installed sumNof initial fresh holderTracked allowZero
    (pairCalls_holderCalls trace apart quiet skim swap burn pairCode noRoot wethSelf) budget

end Blanc.Composition.UniswapV2PairWeth9
