import Blanc.Composition.UniswapV2PairUsdcWeth9BurnEnv
import Blanc.Composition.UniswapV2PairUsdcWeth9BurnLiveF
import Blanc.Composition.UniswapV2PairUsdcWeth9Checkpoint
import Blanc.Composition.UniswapV2PairWeth9BurnLiveOne
import Blanc.Composition.UniswapV2PairWeth9BurnLive
import Blanc.Lift.Usdc.HistoryEnd

/-!
# C6(c): the burn liveness row with both tokens' records discharged (U9 freeze §3c, U9d)

`pair_usdc_weth9_history_burn_live` restates `pair_history_burn_live` from the two-token joint
checkpoint with all six token records pinned (`BurnEnvUW`).  Inside the model's acceptance:

* USDC's initial query runs at the history's end (`usdc_history_end_core`: installed, footprint
  facts); WETH9's initial query reads USDC's result through its skeleton (`burnWethRead1_withGasLeft`);
* USDC's transfer at the suffix's entry world: USDC installed and its storage unchanged there (the
  Pair writes only its own storage, the queries are `STATICCALL`s), `FootCore` over the history's
  universe extended by the recipient's row, and `amount0 ≤` the Pair's USDC balance from the priced
  amount and the first initial answer (`burnFee_amount0_le`); no never-signer premise;
* WETH9's transfer after USDC's, at USDC's result: USDC's post is explicit, so WETH9's code and
  balance word carry across it (`usdcTransferCall_keeps`) and the world-level `burnWethLeg1_spec`
  applies;
* USDC's final query after WETH9's transfer: USDC's codes and slots cross WETH9's explicit post
  (`wethTransferCall_storOff`); WETH9's final query reads USDC's through its skeleton.

No HASH-T premise over the factory query's child is needed: WETH9's legs here need only codes and
storage words, which a `STATICCALL` keeps.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint Blanc.Composition.UniswapV2PairWeth9Joint
  Blanc.Composition.UsdcToken Blanc.Composition.UsdcLive

/-- **C6(c), the burn liveness row with both tokens' records discharged** (USDC = token0, WETH9 =
token1).  As `pair_history_burn_live`, from the two-token joint checkpoint, with USDC's initial
query, transfer and final query and WETH9's pinned in `callee` to the legs the tokens' codes
determine.  What stays is the factory `feeTo` record, the Pair's charges and sentries, the LP rows'
HASH-T, the frame's call depth, the Pair not USDC's admin
word, HASH-T for the recipient's USDC row, USDC's state conditions at the frame (`usdcLive`: not
paused, Pair and recipient unflagged, credit within the packed word, parties nonzero), and the legs'
gas sentries.  USDC's transfer is covered by its own queried balance (`burnAmount_le_balance`), so
no never-signer premise. -/
theorem pair_usdc_weth9_history_burn_live {pair usdc weth : Adr} {cfg : ChainConfig}
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
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44) (depth : 2 ≤ sevm.depth)
    (notAdmin : pair ≠ Usdc.adminOf pre.state usdc)
    (callee : BurnEnvUW sevm pre g) (usdcSentries : callee.UsdcSentries)
    (wethSentries : callee.WethSentries)
    (recipientFresh : Usdc.KeysFresh (Usdc.historyKeyUniverse usdc trace KU)
      [.bal (Sevm.dataWord sevm 4).toAdr])
    (usdcLive : UsdcTransferOk
      (Usdc.ledger (SlotFootprint.extendBy (Usdc.historyKeyUniverse usdc trace KU)
        [.bal (Sevm.dataWord sevm 4).toAdr]) (pre.state.getStor usdc))
      pair (Sevm.dataWord sevm 4).toAdr callee.words.amount0.toNat)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace KP)
      (lpMintTouched sevm.currentTarget ++ lpMintTouched callee.feeTo)) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final0 →
        transcript.ownTail.ownTail.ownTail.ownTail.ownTail.ownTail.firstWord = callee.final1 →
        (runTyped finish (writerContext sevm []) (.burn (Sevm.dataWord sevm 4).toAdr)
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
  exact pair_usdc_weth9_history_burn_live_finite trace joint.toF pairFresh usdcFresh wethFresh
    governance factoryInstalled factoryNotSystem target state codeEq fork output representable
    value size guard selector depth notAdmin callee usdcSentries wethSentries recipientFresh
    usdcLive rowsFresh

end Blanc.Composition.UniswapV2PairUsdcWeth9
