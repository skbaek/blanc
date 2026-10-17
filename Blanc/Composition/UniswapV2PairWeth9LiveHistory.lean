import Blanc.Composition.UniswapV2PairWeth9Joint
import Blanc.Lift.Weth9.FootHistory

/-!
# C4(b): what the history gives a new Pair frame about WETH9 (U8d)

The C4(b) liveness rows discharge the WETH9 callee records of a new Pair frame whose pre-state is
the history's future world.  They need, at that world, facts about WETH9 and about the Pair's own
words that only the history supplies:

* `pair_weth9_end` — C3's positional walk at the history's end, keeping the fixed tokens and the
  open lock (`pair_weth9_joint` keeps only the reserve and allowance facts);
* `pair_weth9_frame` — at the new frame: WETH9's deployed code persists
  (`weth9_history_footprint_universe`), the Pair's stored token word on `side` is WETH9, the lock is
  open, and the stored reserve on `side` is at most the Pair's stored WETH9 balance word (C3).

Premises: the joint checkpoint, both HASH-T premises and the factory premises (A14), as
`pair_weth9_joint` takes them.  Nothing about WETH9's answers.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token
  Blanc.Lift.UniswapV2Pair Blanc.Composition.Weth9Token Blanc.Composition.PairTokenJoint

/-- The Pair's storage slot holding the token on `side`. -/
def tokenSlotOn : TokenSide → B256
  | .zero => 6
  | .one => 7

/-- The reserve on `side` read out of the packed reserve word. -/
def reserveReadOn : TokenSide → B256 → B256
  | .zero => reserve0Read
  | .one => reserve1Read

/-- **C3 at the history's end, keeping the tokens and the lock.**  Over the Pair's full replay the
model state `finish` has WETH9 on `side`, an open lock, and its reserve on `side` at most the Pair's
stored WETH9 balance word. -/
theorem pair_weth9_end {pair weth : Adr} (side : TokenSide)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ side checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧ finish.tokenOn side = weth ∧
        finish.unlocked = 1 ∧
        finish.reserveOn side ≤ ((future.state.getStor weth).get (balSlot pair)).toNat := by
  obtain ⟨hist, answerable, start⟩ := JointCheckpoint.toCore trace joint wethFresh
  have factoryQuiet := UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.pairCode
    factoryInstalled joint.pairNonzero factoryNotSystem
  have walk := pair_token_walk (weth9Core weth K₀) weth9Book_laws weth9Book_erc20Abi
    (weth9SelfCaller weth K₀) side trace joint.pairCode joint.pairRep pairFresh hist joint.token
    joint.unlocked joint.apart answerable joint.distinct joint.notSystem factoryQuiet
    (weth9_tokenEntered trace joint)
  obtain ⟨-, finish, K', replayed⟩ := pair_history_replayed trace joint.pairCode joint.pairRep
    pairFresh
  obtain ⟨steps, observed, auth, replay, -⟩ := id replayed
  obtain ⟨l', run', reserve, -, tokens, opened, -⟩ := walk steps replay auth observed (pre := [])
    (post := []) (by rw [List.nil_append, List.append_nil]) (PairClosed.nil pair)
    (settledFrames_pairClosed trace) ⟨rfl, rfl, rfl⟩ joint.unlocked rfl start.1 start.2
  rw [List.nil_append, (weth9Core weth K₀).replayEnd trace hist] at run'
  cases run'
  refine ⟨finish, K', replayed, ?_, opened, ?_⟩
  · rw [← joint.token]
    cases side
    · exact tokens.1
    · exact tokens.2.1
  · have trackedPair : historyKeyUniverse weth trace K₀ (.bal pair) := Or.inl joint.tracked
    change finish.reserveOn side ≤
      (tracked (historyKeyUniverse weth trace K₀) (future.state.getStor weth) pair).toNat at reserve
    rwa [tracked_self trackedPair] at reserve

/-- **What a new Pair frame at the history's future world knows about WETH9.**  WETH9's deployed
code is installed, the Pair's token word on `side` is WETH9, the lock is open, and the reserve on
`side` is at most the Pair's stored WETH9 balance word (C3 at the history's end). -/
theorem pair_weth9_frame {pair weth : Adr} (side : TokenSide)
    {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    {KP : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ side checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {pre : Devm} (state : pre.state = future.state) :
    pre.state.getCode weth = Weth9.code ∧
      ((pre.getStor pair).get (tokenSlotOn side)).toAdr = weth ∧
      (pre.getStor pair).get 12 = 1 ∧
      (reserveReadOn side ((pre.getStor pair).get 8)).toNat ≤
        ((pre.getStor weth).get (balSlot pair)).toNat := by
  obtain ⟨finish, K', replayed, token, opened, reserve⟩ :=
    pair_weth9_end side trace joint pairFresh wethFresh factoryInstalled factoryNotSystem
  obtain ⟨-, -, -, -, -, -, -, rep⟩ := replayed
  have storPair : pre.getStor pair = future.state.getStor pair :=
    congrArg (fun w : Jaune.State => w.getStor pair) state
  have storWeth : pre.getStor weth = future.state.getStor weth :=
    congrArg (fun w : Jaune.State => w.getStor weth) state
  obtain ⟨-, -, -, slot6, slot7, read0, read1, -, -, -, -, slot12⟩ := rep.fixed
  have futureCode := (weth9_history_footprint_universe trace joint.wethCode joint.sumNof
    joint.wethFoot wethFresh).1
  refine ⟨by rw [state]; exact code_eq_of_image futureCode, ?_, ?_, ?_⟩
  · rw [storPair, ← token]
    cases side
    · exact slot6
    · exact slot7
  · rw [storPair, slot12, opened]
  · rw [storPair, storWeth]
    have small : ∀ x : Fin (2 ^ 112), (Nat.toB256 x.val).toNat = x.val := fun x =>
      B256.toNat_toB256_of_lt (lt_trans x.isLt (by decide : 2 ^ 112 < 2 ^ 256))
    cases side
    · change (reserve0Read ((future.state.getStor pair).get 8)).toNat ≤ _
      rw [read0, small]
      exact reserve
    · change (reserve1Read ((future.state.getStor pair).get 8)).toNat ≤ _
      rw [read1, small]
      exact reserve

end Blanc.Composition.UniswapV2PairWeth9Joint
