import Blanc.Composition.UniswapV2PairWeth9CapstoneShare
import Blanc.Composition.UniswapV2PairWeth9CapstoneTrace
import Blanc.Composition.UniswapV2PairWeth9CapstoneWorld

/-!
# C6(b): from any world agreeing with `W0`, the closed block runs and the headlines apply

`uniswap_weth9_closed_agreeing` (goal C6(b), universal form, amendment A13): for every canonical
world `st` with representable total ether that agrees with `W0` on the touched accounts, the
configured BPO2 block with `signedTx1` (`X.transfer(pair, 1000)`) then `signedTx2`
(`pair.swap(0, 996, trader, "")`) is a valid state transition from the checkpoint at `st`, and on its
configured history

* WETH9's ledger moved `996` from the Pair to the trader;
* the Pair's stored reserves are its new `X` and WETH9 balances (`1001000`, `999004`);
* C3 (`pair_weth9_joint`) holds, every hypothesis discharged;
* C4(a) (`pair_weth9_history_feeOff_product`, WETH9 on side `one`; `W0`'s factory has no `feeTo`)
  holds with its `X`-side antecedent discharged (the history's only Pair step is the swap, whose
  `EntryNoShrinkSide` is `True`; decision uw9-c6-swap-kept), and share value strictly increases from
  `W0`'s Pair state to the history's end at equal supply (`10^6 · 10^6 < 1001000 · 999004`).

Discharged on the way: signature recovery (kernel, U10c), both transactions' contexts (from the
agreement), the system fixture before and after, the joint checkpoint (transported from
`w0_jointCheckpoint`), the factory premises (`w0_factoryInstalled`, A14), and both HASH-T premises
for this concrete history (`history_wethFresh`, `history_pairFresh`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.ExecutionTrace Blanc.BlockForward
  Blanc.Composition.UniswapV2PairWeth9Instance Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UniswapV2PairWeth9ShareValue Blanc.Composition.PairTokenShareValue
open Blanc.Lift.Weth9.ClosedInstance (config checkpoint input systemAddresses)

/-- The world after both transactions. -/
abbrev swapWorld (st : Jaune.State) : Jaune.State := tx2SettledState (tx1World st)

/-- `W0`'s Pair model state. -/
abbrev w0PairState : UniswapV2Pair.State := UniswapV2Pair.rowsState w0Base w0PairRows

/-- **What the closed block does on `st`**: it is a valid configured state transition from the
checkpoint at `st`, and on a configured history of it WETH9's ledger moved `996` from the Pair to
the trader, the Pair's reserves are its new balances, C3 holds, and C4(a) holds with its `X`-side
antecedent discharged, share value rising strictly from `W0`'s Pair state at equal supply. -/
def ClosedSwapOutcome (st : Jaune.State) : Prop :=
  ∃ bout : BlockOutput,
    stateTransitionUsing config (checkpoint st) (swapBlock st (swapWorld st) bout) =
      .ok (swapChain st (swapWorld st) bout) ∧
    ∃ trace : ConfiguredHistoryTrace config (checkpoint st) (swapChain st (swapWorld st) bout),
      -- WETH9's ledger: the trader gains `996`, the Pair loses `996`
      ((swapWorld st).getStor weth).get (Weth9.balSlot trader) =
          (st.getStor weth).get (Weth9.balSlot trader) + swapOut ∧
        ((swapWorld st).getStor weth).get (Weth9.balSlot pair) =
          (st.getStor weth).get (Weth9.balSlot pair) - swapOut ∧
        ((swapWorld st).getStor weth).get (Weth9.balSlot trader) = 996 ∧
        ((swapWorld st).getStor weth).get (Weth9.balSlot pair) = 999004 ∧
      -- the reserves are the new balances
        reserve0Read (((swapWorld st).getStor pair).get 8) =
          ((swapWorld st).getStor tokenX).get (VyperNonreentrantDeployed.Token20.balSlot pair) ∧
        reserve1Read (((swapWorld st).getStor pair).get 8) =
          ((swapWorld st).getStor weth).get (Weth9.balSlot pair) ∧
        reserve0Read (((swapWorld st).getStor pair).get 8) = 1001000 ∧
        reserve1Read (((swapWorld st).getStor pair).get 8) = 999004 ∧
      -- C3 over the history, every hypothesis discharged
        ((∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
          trace.settledFrames = before ++ f :: after →
          (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
          ∃ (s : UniswapV2Pair.State) (K : WriterKey → Prop),
            WriterRep K (f.pre.state.getStor pair) s ∧ s.unlocked = 1 ∧ s.tokenOn .one = weth ∧
              s.reserveOn .one ≤ ((Weth9.ledger (Weth9.historyKeyUniverse weth trace
                (FiniteCheckpoint.rowKeys w0WethRows)) (f.pre.state.getStor weth)).bal pair).toNat ∧
              ∀ g, (Weth9.ledger (Weth9.historyKeyUniverse weth trace
                (FiniteCheckpoint.rowKeys w0WethRows)) (f.pre.state.getStor weth)).allow pair g = 0) ∧
        ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
          PairHistoryReplayed pair trace (UniswapV2Pair.pairKeys w0PairRows) w0PairState finish K' ∧
            finish.reserveOn .one ≤ (((swapWorld st).getStor weth).get (Weth9.balSlot pair)).toNat ∧
            ∀ g, Weth9.historyKeyUniverse weth trace (FiniteCheckpoint.rowKeys w0WethRows)
                (.allow pair g) → ((swapWorld st).getStor weth).get (Weth9.allowSlot pair g) = 0) ∧
      -- C4(a) over the history, its `X`-side antecedent discharged; strict increase at equal supply
        ∃ steps : List PairStep,
          steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
          (∀ s ∈ steps, s.AuthenticWith PairEntryAuth pair) ∧
          ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
            PairObservedReplayWith PairAdmittedConsumes w0PairState steps finish ∧
            runSourceInvocations w0PairState (steps.map PairStep.source) = some finish ∧
            WriterRep K' ((swapWorld st).getStor pair) finish ∧
            (∀ before after,
              (before, after) ∈ sourceReplayEdges w0PairState (steps.map PairStep.source) →
              0 < before.totalSupply.toNat →
              before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
                after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2) ∧
            finish.reserve0.val = 1001000 ∧ finish.reserve1.val = 999004 ∧
            finish.totalSupply = w0PairState.totalSupply ∧
            w0PairState.reserve0.val * w0PairState.reserve1.val * finish.totalSupply.toNat ^ 2 <
              finish.reserve0.val * finish.reserve1.val * w0PairState.totalSupply.toNat ^ 2

/-- **C6(b), universal form**: every canonical world with representable total ether agreeing with
`W0` on the touched accounts. -/
theorem uniswap_weth9_closed_agreeing {st : Jaune.State} (canonical : st.Canonical)
    (bound : SumNof st.bal) (ag : AgreesW0 st) : ClosedSwapOutcome st := by
  -- the two transactions
  have ctx1 := tx1Context_of_agrees ag
  obtain ⟨bout1, run1, used1, -, keys1, receipt1, -⟩ := tx1_transaction ctx1 tx1_recoveredSender
  have ctx2 := tx2Context_of_agrees ag
  obtain ⟨bout2, run2, -, -, -, -, -, requests2, gas2⟩ := tx2_transaction ctx2 used1 keys1
    (by
      intro key hk
      rw [keys1, List.mem_singleton] at hk
      subst hk
      exact ⟨_, receipt1, fun log hlog => absurd hlog List.not_mem_nil⟩)
    tx2_recoveredSender
  -- the configured history
  obtain ⟨transition, trace, t1, t2, sysRaw, sysRaw', -, -, raw, -, sysR, -⟩ :=
    swap_history canonical bound (systemCodes_of_agrees ag) (systemCodes_after ag) run1 run2
      requests2 gas2
  -- its raw frames
  have one := tx1_trace_raw ctx1 t1
  obtain ⟨sevm, b, G, h, out, run, t2eq⟩ := tx2_trace_raw ctx2 used1 t2
  have callees := (tx2_swap_raw h run).2
  have frames : trace.rawFrames = sysRaw ++ t1.rawFrames ++ Exec.rawFrameRoots run ++ sysRaw' :=
    raw.trans (congrArg (fun l => sysRaw ++ t1.rawFrames ++ l ++ sysRaw') t2eq)
  have cases := history_roots_cases frames sysR one callees
  have cases' : ∀ D ∈ trace.rawFrames, D.sevm.currentTarget ∈ systemAddresses ∨
      D.sevm.currentTarget = tokenX ∨ D.sevm.currentTarget = pair ∨ Tx2Callee D := by
    intro D hD
    rcases cases D hD with c | c | rfl | c
    · exact Or.inl c
    · exact Or.inr (Or.inl c)
    · exact Or.inr (Or.inr (Or.inl h.target))
    · exact Or.inr (Or.inr (Or.inr c))
  -- the headlines' premises
  have wethFresh := history_wethFresh cases'
  have pairFresh := history_pairFresh h cases
  have joint := jointCheckpoint_of_agrees ag bound
  have fac := factory_of_agrees ag
  have c3 := pair_weth9_joint .one trace joint pairFresh wethFresh fac.1 fac.2
  obtain ⟨steps, observed, auth, finish, K', replay, runs, rep, product⟩ :=
    pair_weth9_history_feeOff_product .one trace joint pairFresh wethFresh fac.1 fac.2
  have answers : sourceReplayAnswersSide TokenSide.zero w0PairState (steps.map PairStep.source) :=
    answersSide_of_swaps (history_steps_swap h cases observed auth)
  -- the world facts
  have s1weth : (tx1World st).getStor weth = st.getStor weth := by
    change ((tx1World st).get weth).stor = (st.get weth).stor
    rw [tx1World_other (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  have stWeth : st.getStor weth = w0WethStor := by
    change (st.get weth).stor = _; rw [agrees_weth ag, W0_weth]
  have balances := tx2_settled_weth_balances ctx2
  change ((swapWorld st).getStor weth).get (Weth9.balSlot trader) =
      ((tx1World st).getStor weth).get (Weth9.balSlot trader) + swapOut ∧
    ((swapWorld st).getStor weth).get (Weth9.balSlot pair) =
      ((tx1World st).getStor weth).get (Weth9.balSlot pair) - swapOut at balances
  rw [s1weth] at balances
  have traderAfter : ((swapWorld st).getStor weth).get (Weth9.balSlot trader) = 996 := by
    rw [balances.1, stWeth, w0WethStor_trader]; decide
  have pairAfter : ((swapWorld st).getStor weth).get (Weth9.balSlot pair) = 999004 := by
    rw [balances.2, stWeth, w0WethStor_pair]; decide
  obtain ⟨res0, res1, -, -⟩ := tx2_settled_reserves (tx1World st)
  have xAfter : ((swapWorld st).getStor tokenX).get
      (VyperNonreentrantDeployed.Token20.balSlot pair) = 1001000 := by
    change ((swapWorld st).get tokenX).stor.get _ = _
    rw [tx2_settled_get_other _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)]
    exact ctx2.xPair
  -- the Pair's state at the history's end
  have fixed : WriterFixedMatches ((tx2SettledState (tx1World st)).getStor pair) finish := rep.fixed
  unfold WriterFixedMatches at fixed
  rw [res0] at fixed
  have r0 : finish.reserve0.val = 1001000 := by
    have e := congrArg B256.toNat fixed.2.2.2.2.2.1
    rw [B256.toNat_toB256_of_lt (Nat.lt_trans finish.reserve0.isLt (by decide))] at e
    rw [← e]; decide
  rw [res1] at fixed
  have r1 : finish.reserve1.val = 999004 := by
    have e := congrArg B256.toNat fixed.2.2.2.2.2.2.1
    rw [B256.toNat_toB256_of_lt (Nat.lt_trans finish.reserve1.isLt (by decide))] at e
    rw [← e]; decide
  have ts : finish.totalSupply = w0PairState.totalSupply := by
    rw [← fixed.1, tx2_settled_pairStor]
    simp only [Stor.get_set_ne _ (show (12 : B256) ≠ 0 by decide),
      Stor.get_set_ne _ (show (8 : B256) ≠ 0 by decide),
      Stor.get_set_ne _ (show (10 : B256) ≠ 0 by decide),
      Stor.get_set_ne _ (show (9 : B256) ≠ 0 by decide)]
    have s1pair : (tx1World st).getStor pair = w0PairStor := by
      change ((tx1World st).get pair).stor = w0PairStor
      rw [tx1World_other (by decide +kernel) (by decide +kernel) (by decide +kernel), agrees_pair ag,
        W0_pair]
    rw [s1pair]
    exact w0PairStor_0
  unfold ClosedSwapOutcome
  refine ⟨_, transition, trace, balances.1, balances.2, traderAfter, pairAfter, ?_, ?_, res0, res1,
    c3, steps, observed, auth, finish, K', replay, runs, rep, product answers, r0, r1, ts, ?_⟩
  · rw [res0, xAfter]
  · rw [res1, pairAfter]
  · rw [r0, r1, ts]
    decide

end Blanc.Composition.UniswapV2PairWeth9Capstone
