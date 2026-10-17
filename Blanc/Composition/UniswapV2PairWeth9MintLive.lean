import Blanc.Composition.UniswapV2PairWeth9SyncLive
import Blanc.Composition.UniswapV2PairWeth9LegsMint

/-!
# C4(b): the mint liveness row with WETH9's query discharged (U8d)

`pair_history_mint_live` takes `MintPrefixCallee`, whose `tokens` field holds both tokens'
`balanceOf(pair)` `STATICCALL` records.  With WETH9 on one side that side's record is WETH9's own
run: its result and call gas are pinned (`_read`) to `mintWethRead0` / `mintWethRead1` (U8b1) and
its premises are discharged from the history (WETH9's code at the token the Pair loads, WETH9 not
a precompile), plus the frame's call depth and the leg's gas sentries.  The factory `feeTo` record,
the other token's record and the Pair's own charges and sentries stay.

* `MintCalleeRest` — `MintPrefixCallee` without `tokens`; `MintTokenHalf0` / `MintTokenHalf1` —
  one token's half of `MintBalanceForward`;
* `pair_weth9_history_mint_live_zero` (WETH9 = token0), `pair_weth9_history_mint_live_one`
  (WETH9 = token1).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair

/-- The world mint stages its token queries over (after the lock and the reserve cache). -/
def mintCacheWorld (sevm : Sevm) (b : Devm) : Devm := afterSload sevm (mintLockedWorld sevm b) 8

/-- The cached reserves mint reads. -/
def mintR0 (sevm : Sevm) (b : Devm) : B256 :=
  reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)

def mintR1 (sevm : Sevm) (b : Devm) : B256 :=
  reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)

/-- **`MintPrefixCallee` without its token records**: the factory `feeTo` record, the charges
and the sentries. -/
structure MintCalleeRest (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (toWord ρ : B256) (finalGas : Nat) where
  d0 : Devm
  d1 : Devm
  factoryPost : Devm
  callGas0 : Nat
  callGas1 : Nat
  factoryGas : Nat
  feeResidual : Nat
  sourceCost : Nat
  supplyCost : Nat
  recipientLoad : Nat
  creditCost : Nat
  lockLoad : Nat
  lockStore : Nat
  reserveLoad : Nat
  loadEq : lockLoad = sloadCost sevm b 12
  storeEq : lockStore = sstoreCost sevm (afterSload sevm b 12) 12 0
  reserveEq : reserveLoad = sloadCost sevm (mintLockedWorld sevm b) 8
  fee : MintFeePricingCallee sevm d1 factoryPost R
    (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
      sevm.currentTarget d1.returnData)
    feeResidual finalGas factoryGas sourceCost supplyCost recipientLoad creditCost
    (Bytes.toB256 (d1.returnData.take 32)) (Bytes.toB256 (d0.returnData.take 32))
    (mintR1 sevm b) (mintR0 sevm b) toWord ρ
  sentry : gCallStipend < callGas0 + 5 +
    sloadCost sevm (mintCacheWorld sevm b) 6 +
    temporalAccountAccessCost (afterSload sevm (mintCacheWorld sevm b) 6)
      ((mintCacheWorld sevm b).getStorVal sevm.currentTarget 6).toAdr +
    166 + reserveLoad + 87 + lockStore

section Rest

variable {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {toWord ρ : B256} {finalGas : Nat}

/-- The gas the tokens' records leave for the factory call (`MintPrefixCallee.tokens`'s tail). -/
def MintCalleeRest.tokensGas (c : MintCalleeRest sevm b R M toWord ρ finalGas) : Nat :=
  c.factoryGas + sloadCost sevm c.d1 5 +
    temporalAccountAccessCost (feeFactoryLoadWorld sevm c.d1) (feeFactoryWord sevm c.d1).toAdr + 360

def MintCalleeRest.gas (c : MintCalleeRest sevm b R M toWord ρ finalGas) : Nat :=
  c.callGas0 + 5 + sloadCost sevm (mintCacheWorld sevm b) 6 +
    temporalAccountAccessCost (afterSload sevm (mintCacheWorld sevm b) 6)
      ((mintCacheWorld sevm b).getStorVal sevm.currentTarget 6).toAdr + 166 +
    c.reserveLoad + 100 + c.lockStore + c.lockLoad + 26

def MintCalleeRest.balance0 (c : MintCalleeRest sevm b R M toWord ρ finalGas) : B256 :=
  Bytes.toB256 (c.d0.returnData.take 32)

def MintCalleeRest.balance1 (c : MintCalleeRest sevm b R M toWord ρ finalGas) : B256 :=
  Bytes.toB256 (c.d1.returnData.take 32)

def MintCalleeRest.feeTo (c : MintCalleeRest sevm b R M toWord ρ finalGas) : Adr :=
  (Bytes.toB256 (c.factoryPost.returnData.take 32)).toAdr

/-- The rest with both token records is the whole callee environment. -/
def MintCalleeRest.withTokens (c : MintCalleeRest sevm b R M toWord ρ finalGas)
    (t : MintBalanceForward sevm (mintCacheWorld sevm b) c.d0 c.d1 R M c.callGas0 c.callGas1
      c.tokensGas (mintR1 sevm b) (mintR0 sevm b) toWord ρ) :
    MintPrefixCallee sevm b R M toWord ρ finalGas :=
  { d0 := c.d0, d1 := c.d1, factoryPost := c.factoryPost, callGas0 := c.callGas0,
    callGas1 := c.callGas1, factoryGas := c.factoryGas, feeResidual := c.feeResidual,
    sourceCost := c.sourceCost, supplyCost := c.supplyCost, recipientLoad := c.recipientLoad,
    creditCost := c.creditCost, lockLoad := c.lockLoad, lockStore := c.lockStore,
    reserveLoad := c.reserveLoad, loadEq := c.loadEq, storeEq := c.storeEq,
    reserveEq := c.reserveEq, fee := c.fee, tokens := t, sentry := c.sentry }

end Rest

/-- Token0's half of `MintBalanceForward` (its `balanceOf(pair)` record). -/
structure MintTokenHalf0 (sevm : Sevm) (b d0 : Devm) (R : List B256) (M : Mem)
    (callGas0 callGas1 : Nat) (r1 r0 toWord ρ : B256) : Prop where
  code0 : ((afterSload sevm b 6).getCode (b.getStorVal sevm.currentTarget 6).toAdr).size.toB256 ≠ 0
  call0 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm b 6) (b.getStorVal sevm.currentTarget 6).toAdr)
        (callGas0.toB256 :: (b.getStorVal sevm.currentTarget 6).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 0 :: r1 :: r0 ::
          0 :: toWord :: ρ :: R) (balanceRequestMemory M sevm.currentTarget) callGas0)
      (.exec .staticcall) d0
  success0 : d0.stack = 1 :: 164 :: 0x70a08231 ::
      (b.getStorVal sevm.currentTarget 6).toAdr.toB256 :: 0 :: r1 :: r0 :: 0 :: toWord :: ρ :: R
  long0 : 32 ≤ d0.returnData.length
  gas0 : d0.gasLeft = callGas1 + 5 + sloadCost sevm d0 7 +
      temporalAccountAccessCost (afterSload sevm d0 7) (d0.getStorVal sevm.currentTarget 7).toAdr + 219

/-- Token1's half of `MintBalanceForward` (its `balanceOf(pair)` record). -/
structure MintTokenHalf1 (sevm : Sevm) (d0 d1 : Devm) (R : List B256) (M : Mem)
    (callGas1 G : Nat) (r1 r0 toWord ρ : B256) : Prop where
  code1 : ((afterSload sevm d0 7).getCode (d0.getStorVal sevm.currentTarget 7).toAdr).size.toB256 ≠ 0
  call1 : Ninst.RunCompiled sevm
      (St (temporalAccountAccessBase (afterSload sevm d0 7) (d0.getStorVal sevm.currentTarget 7).toAdr)
        (callGas1.toB256 :: (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 ::
          128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 :: 0 ::
          Bytes.toB256 (d0.returnData.take 32) :: r1 :: r0 :: 0 :: toWord :: ρ :: R)
        (balanceRequestMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
          sevm.currentTarget) callGas1) (.exec .staticcall) d1
  success1 : d1.stack = 1 :: 164 :: 0x70a08231 ::
      (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 :: 0 ::
      Bytes.toB256 (d0.returnData.take 32) :: r1 :: r0 :: 0 :: toWord :: ρ :: R
  long1 : 32 ≤ d1.returnData.length
  gas1 : d1.gasLeft = G + 70

theorem mintLockedWorld_slot {sevm : Sevm} {pre : Devm} {k : B256} (hk : (12 : B256) ≠ k) :
    (mintCacheWorld sevm pre).getStorVal sevm.currentTarget k =
      pre.getStorVal sevm.currentTarget k := by
  change (Devm.getStor (mintCacheWorld sevm pre) sevm.currentTarget).get k =
    (Devm.getStor pre sevm.currentTarget).get k
  unfold mintCacheWorld mintLockedWorld
  rw [afterSload_getStor, afterSstore_getStor_self, Stor.get_set_ne _ hk, afterSload_getStor]

theorem mintCacheWorld_keeps (sevm : Sevm) (pre : Devm) {w : Adr} (ne : sevm.currentTarget ≠ w) :
    WethKeeps w pre (afterSload sevm (mintCacheWorld sevm pre) 6) :=
  (((WethKeeps.afterSload sevm pre 12).trans (WethKeeps.afterSstore ne _ 12 0)).trans
    (WethKeeps.afterSload sevm _ 8)).trans (WethKeeps.afterSload sevm _ 6)

/-- **C4(b), the mint liveness row with WETH9 as token0.**  As `pair_history_mint_live`, from the
joint checkpoint, with WETH9's `balanceOf(pair)` record removed: its result and call gas are
pinned to `mintWethRead0`.  What stays is token1's record (`token1`), the factory record and the
charges (`callee`), the frame's call depth, the leg's gas sentries and the LP rows' HASH-T. -/
theorem pair_weth9_history_mint_live_zero {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .zero checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842) (depth : sevm.depth ≠ 0)
    (callee : MintCalleeRest sevm pre [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (_read : (callee.d0, callee.callGas0) = mintWethRead0 sevm (mintCacheWorld sevm pre)
      [0x6a627842] getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.callGas1)
    (fits : callee.callGas0 < 2 ^ 256)
    (room : balUsed sevm (afterSload sevm (mintCacheWorld sevm pre) 6)
        (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
        (mintToken0 sevm (mintCacheWorld sevm pre)) ≤
      except64th (mintRead0Need sevm callee.callGas1 (wethBalanceSkel sevm
          (afterSload sevm (mintCacheWorld sevm pre) 6)
          (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
          (mintToken0 sevm (mintCacheWorld sevm pre))) +
        balUsed sevm (afterSload sevm (mintCacheWorld sevm pre) 6)
          (mintTail0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b) getterInitMemory 128
          (mintToken0 sevm (mintCacheWorld sevm pre))))
    (token1 : MintTokenHalf1 sevm callee.d0 callee.d1 [0x6a627842] getterInitMemory callee.callGas1
      callee.tokensGas (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace KP)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        (runTyped finish (writerContext sevm []) (.mint (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ (liquidity : B256)
          (run : Exec 0 sevm (St pre [] Mem.empty (callee.gas + 228))
            (.ok (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G))),
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).gasLeft = G ∧
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).output =
            liquidity.toBytes ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace KP)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace KP)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) := by
  have h0 : (mintWethRead0 sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
      (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b
      callee.callGas1).1 = callee.d0 := (congrArg Prod.fst _read).symm
  have hg : (mintWethRead0 sevm (mintCacheWorld sevm pre) [0x6a627842] getterInitMemory
      (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b
      callee.callGas1).2 = callee.callGas0 := (congrArg Prod.snd _read).symm
  obtain ⟨code, token, -, -⟩ := pair_weth9_frame .zero trace joint pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have tok : ((mintCacheWorld sevm pre).getStorVal sevm.currentTarget 6).toAdr = weth := by
    rw [mintLockedWorld_slot (by decide), target]
    exact token
  have wcode : (afterSload sevm (mintCacheWorld sevm pre) 6).state.getCode
      ((mintCacheWorld sevm pre).getStorVal sevm.currentTarget 6).toAdr = Weth9.code := by
    rw [tok]
    exact (mintCacheWorld_keeps sevm pre (target ▸ joint.apart)).1.trans code
  have np : sevm.benvStat.rules.isPrecomp
      ((mintCacheWorld sevm pre).getStorVal sevm.currentTarget 6).toAdr = (false = true) := by
    rw [tok]
    exact notPrecompile_of_joint joint fork
  have spec := mintWethRead0_spec fork depth wcode np (by decide) getterInitMemory_ptr.wf
    (by rw [hg]; exact fits) room
  dsimp only at spec
  rw [h0, hg] at spec
  obtain ⟨code0, call0, success0, gas0, long0, -⟩ := spec
  exact pair_history_mint_live trace joint.pairCode joint.pairRep pairFresh target state codeEq
    fork output representable value size guard selector
    (callee.withTokens ⟨code0, call0, success0, long0, token1.code1, token1.call1, token1.success1,
      token1.long1, gas0, token1.gas1⟩) rowsFresh

/-- **C4(b), the mint liveness row with WETH9 as token1.**  As `pair_history_mint_live`, from the
joint checkpoint, with WETH9's `balanceOf(pair)` record removed: its result and call gas are
pinned to `mintWethRead1` over token0's result.  What stays is token0's record (`token0`), the
factory record and the charges (`callee`), the frame's call depth, the leg's gas sentries and the
LP rows' HASH-T. -/
theorem pair_weth9_history_mint_live_one {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .one checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
    (factoryInstalled :
      some (checkpoint.state.getCode st₀.factory).toList = UniswapV2Factory.factorySem.image)
    (factoryNotSystem : st₀.factory ≠ systemAddress)
    {sevm : Sevm} {pre : Devm} {G : Nat}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (guard : (32 : B256) ≤ sevm.data.length.toB256 - 4)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842) (depth : sevm.depth ≠ 0)
    (callee : MintCalleeRest sevm pre [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (token0 : MintTokenHalf0 sevm (mintCacheWorld sevm pre) callee.d0 [0x6a627842] getterInitMemory
      callee.callGas0 callee.callGas1 (mintR1 sevm pre) (mintR0 sevm pre)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
    (_read : (callee.d1, callee.callGas1) = mintWethRead1 sevm callee.d0 [0x6a627842]
      getterInitMemory (mintR1 sevm pre) (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256
      0x039b callee.factoryGas)
    (fits : callee.callGas1 < 2 ^ 256)
    (room : balUsed sevm (afterSload sevm callee.d0 7)
        (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
          (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
        (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
        (syncToken1 sevm callee.d0) ≤
      except64th (mintRead1Need sevm callee.factoryGas (wethBalanceSkel sevm
          (afterSload sevm callee.d0 7)
          (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
          (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
          (syncToken1 sevm callee.d0)) +
        balUsed sevm (afterSload sevm callee.d0 7)
          (mintTail1 callee.d0 [0x6a627842] (mintR1 sevm pre) (mintR0 sevm pre)
            (Sevm.dataWord sevm 4).toAdr.toB256 0x039b)
          (balanceReplyMemory getterInitMemory sevm.currentTarget callee.d0.returnData) 128
          (syncToken1 sevm callee.d0)))
    (rowsFresh : WriterFreshKeys (pairHistoryUniverse pair trace KP)
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord sevm 4).toAdr ++
        lpMintTouched callee.feeTo)) :
    ∃ (finish : UniswapV2Pair.State) (K' : WriterKey → Prop),
      PairHistoryReplayed pair trace KP st₀ finish K' ∧
      ∀ (transcript : Transcript) (returndata : Bytes),
        transcript.firstWord = callee.balance0 → transcript.ownTail.firstWord = callee.balance1 →
        transcript.ownTail.ownTail.firstWord.toAdr = callee.feeTo →
        (runTyped finish (writerContext sevm []) (.mint (Sevm.dataWord sevm 4).toAdr)
          transcript).status = .success returndata →
        ∃ (liquidity : B256)
          (run : Exec 0 sevm (St pre [] Mem.empty (callee.gas + 228))
            (.ok (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G))),
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).gasLeft = G ∧
          (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G).output =
            liquidity.toBytes ∧
          (WriterFreshKeys (pairHistoryUniverse pair trace KP)
              (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩) →
            PairAdmittedOutcome
              (WriterExtend (pairHistoryUniverse pair trace KP)
                (pairDerivKeys ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩))
              { state := finish, logs := [], updates := [] } [] K'
              ⟨0, sevm, St pre [] Mem.empty (callee.gas + 228), .ok _, run⟩
              (getterWordPost callee.fee.post [0x6a627842] callee.fee.post.memory liquidity G)) := by
  have h1 : (mintWethRead1 sevm callee.d0 [0x6a627842] getterInitMemory (mintR1 sevm pre)
      (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.factoryGas).1 =
      callee.d1 := (congrArg Prod.fst _read).symm
  have hg : (mintWethRead1 sevm callee.d0 [0x6a627842] getterInitMemory (mintR1 sevm pre)
      (mintR0 sevm pre) (Sevm.dataWord sevm 4).toAdr.toB256 0x039b callee.factoryGas).2 =
      callee.callGas1 := (congrArg Prod.snd _read).symm
  obtain ⟨code, token, -, -⟩ := pair_weth9_frame .one trace joint pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have ne : sevm.currentTarget ≠ weth := target ▸ joint.apart
  have staged := (mintCacheWorld_keeps sevm pre ne).trans (WethKeeps.access (w := weth)
    (afterSload sevm (mintCacheWorld sevm pre) 6)
    ((mintCacheWorld sevm pre).getStorVal sevm.currentTarget 6).toAdr)
  have afterX := staged.trans (WethKeeps.staticcall fork token0.call0
    (weth9_code_toList_ne (staged.1.trans code)))
  have slot7 : callee.d0.getStorVal sevm.currentTarget 7 = pre.getStorVal sevm.currentTarget 7 := by
    change (Devm.getStor callee.d0 sevm.currentTarget).get 7 =
      (Devm.getStor pre sevm.currentTarget).get 7
    rw [compiled_staticcall_stor fork token0.call0, temporalAccountAccessBase_getStor,
      afterSload_getStor]
    exact mintLockedWorld_slot (by decide)
  have tok : (callee.d0.getStorVal sevm.currentTarget 7).toAdr = weth := by
    rw [slot7, target]
    exact token
  have wcode : (afterSload sevm callee.d0 7).state.getCode
      (callee.d0.getStorVal sevm.currentTarget 7).toAdr = Weth9.code := by
    rw [tok]
    exact ((afterX.trans (WethKeeps.afterSload sevm callee.d0 7)).1).trans code
  have np : sevm.benvStat.rules.isPrecomp
      (callee.d0.getStorVal sevm.currentTarget 7).toAdr = (false = true) := by
    rw [tok]
    exact notPrecompile_of_joint joint fork
  have spec := mintWethRead1_spec fork depth wcode np (by decide) getterInitMemory_ptr.wf
    (by rw [hg]; exact fits) room
  dsimp only at spec
  rw [h1, hg] at spec
  obtain ⟨code1, call1, success1, gas1, long1, -⟩ := spec
  exact pair_history_mint_live trace joint.pairCode joint.pairRep pairFresh target state codeEq
    fork output representable value size guard selector
    (callee.withTokens ⟨token0.code0, token0.call0, token0.success0, token0.long0, code1, call1,
      success1, long1, token0.gas0, gas1⟩) rowsFresh

end Blanc.Composition.UniswapV2PairWeth9Joint
