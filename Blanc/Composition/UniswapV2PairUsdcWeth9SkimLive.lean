import Blanc.Composition.UniswapV2PairUsdcWeth9SkimEnv
import Blanc.Composition.UniswapV2PairUsdcWeth9Joint
import Blanc.Composition.UniswapV2PairUsdcWeth9SkimLiveF
import Blanc.Composition.UniswapV2PairWeth9SkimLiveOne
import Blanc.Lift.Usdc.HistoryEnd
import Blanc.Lift.UniswapV2Pair.SkimForwardKept

/-!
# C6(c): the skim liveness row with both tokens' records discharged (U9e)

USDC = `token0`, WETH9 = `token1`.  `pair_history_skim_live` takes `SkimForwardEnv`; all four token
records are pinned in `SkimCalleeUW` and discharged here:

* USDC's query (`skimUsdcRead0_spec`) and transfer (`skimUsdcLeg0_spec`) at the world facts the
  history's end gives (`usdc_history_end_core`: installed, admin unchanged, the footprint facts),
  carried across Skim's own prefix (Pair storage only) and the query (a view: `usdcBalanceCall_state`).
  The transfer amount `answer − reserve0` does not wrap because C6(a) bounds the Pair's reserve0 by
  its stored USDC balance at the history's end (`pair_usdc_weth9_joint`), and the answer is that
  balance.  The recipient's row joins the universe by `recipientFresh`.
* WETH9's query and transfer (`skimWethLeg1_of_kept`): USDC's transfer is an explicit post that
  keeps every other account's storage and every code (`usdcTransferCall_keeps`), so WETH9's code and
  the Pair's reserve1 word and WETH9 balance at the transfer's result are the frame's, where the
  WETH9 joint bounds reserve1 (`pair_weth9_frame`).
* The same keeps fact gives the forward run's reserve1 re-read after USDC's transfer
  (`SkimForwardEnv.run_of_kept`), so the generic row's trace-local HASH-T for the first transfer
  (`FirstCallFresh`) is not needed.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.UsdcLive

/-- **C6(c), the skim liveness row with both tokens' records discharged** (USDC = token0, WETH9 =
token1).  As `pair_history_skim_live`, from the two-token joint checkpoint, with both queries and
both transfers pinned in `callee`.  USDC's transfer amount is the queried balance less the cached
reserve0; it does not wrap because the model's acceptance of skim at the replayed state bounds
reserve0 by the queried balance (decision usdc-u9e-premise-trim: no never-signer premise).  What
stays is the lock sentries, the frame's call depth and
mutability, the Pair not USDC's admin word, HASH-T for the recipient's USDC row, USDC's state
conditions at the frame, and the legs' gas sentries. -/
theorem pair_usdc_weth9_history_skim_live {pair usdc weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {KU : Usdc.Key → Prop} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint2 pair usdc weth KU KW KP st₀ checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (usdcFresh : Usdc.KeysFresh KU (Usdc.historyTouchedKeys usdc trace))
    (wethFresh : Weth9.KeysFresh KW (Weth9.historyTouchedKeys weth trace))
    (governance : Usdc.UsdcGovernance usdc trace)
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} {g : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (abi : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (static : sevm.isStatic = false) (depth : 2 ≤ sevm.depth)
    (notAdmin : pair ≠ Usdc.adminOf pre.state usdc)
    (callee : SkimCalleeUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc trace KU)
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace KU)
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr (callee.balance0 - skimReserve0 sevm pre).toNat) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 →
        transcript.ownTail.ownTail.firstWord = callee.balance1 →
        (runTyped finish (writerContext sevm []) (.skim (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ run : Exec 0 sevm (St pre [] Mem.empty callee.gas) (.ok callee.post),
          callee.post.gasLeft = g ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace KP)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace KP)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty callee.gas, .ok _, run⟩ callee.post) := by
  exact pair_usdc_weth9_history_skim_live_finite trace joint.toF pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size abi selector static depth notAdmin callee usdcSentries wethSentries recipientFresh
    usdcLive

end Blanc.Composition.UniswapV2PairUsdcWeth9
