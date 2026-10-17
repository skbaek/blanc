import Blanc.Composition.UniswapV2PairWeth9SkimEnvOne
import Blanc.Composition.UniswapV2PairWeth9SwapLiveBothFacts

/-!
# C4(b): the skim liveness row with WETH9 = token1 (U8h)

`pair_history_skim_live` takes `SkimForwardEnv`.  With WETH9 as token1, Skim queries and pays
X = token0 first (`qenv0`, `tenv0`, X's records), then reloads reserve1, queries WETH9 (`qenv1`) and
pays it (`tenv1`).  WETH9's query and transfer are pinned (`SkimCalleeW1`: `gasT1`, `read`, `leg`)
and discharged by `skimWethLeg1_of_read`, from the world facts at X's query result `qd0`:

* WETH9's code, footprint and the ether-supply bound (`WethFootAt`), from the history's end across
  Skim's own prefix and X's query (`static_foot`, HASH-T over the query child's WETH9 keys);
* the Pair's WETH9 allowances zero (C3), the Pair runtime with the locked representation (the lock
  write, then a `STATICCALL`), the factory runtime at that state's factory;
* `cover`: the reserve1 word Skim reloads after X's transfer is at most the Pair's WETH9 balance at
  `qd0`.  X's transfer child leaves the locked Pair's reserve1 (`skimFirstCall_reserve1`, under the
  same trace-local HASH-T `FirstCallFresh` the generic row takes), so the word is the one at `qd0`,
  which is the one at the history's end, and C3 bounds it by the Pair's WETH9 balance there, which
  the queries and the Pair's own steps leave alone.

Added premises (none mentions WETH9's answers): HASH-T over the WETH9 keys of X's query child and
of X's transfer child, and over the Pair rows of X's transfer child (A16 addendum); the legs' call
gases words and their 63/64 sentries; the frame's depth and mutability.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair
open Blanc.Composition.UniswapV2PairWeth9XLeg (CallChildFresh StaticChildFresh wethRunKeys
  pairRunKeys)

section W1

variable {sevm : Sevm} {b : Devm} {g : Nat}

/-- X's transfer `CALL`'s staged state, in the X-leg's form. -/
def SkimCalleeW1.xferPre (env : SkimCalleeW1 sevm b g) : Devm :=
  xferCallState env.qd0 (skimLegStack sevm b) (skimLegMem sevm env.qd0) 128
    (skimLegAmount sevm b env.qd0) (skimToWord sevm) (skimToken0 sevm b) 0x1a2b env.callGasT0

/-- **HASH-T over X's children.**  The keys the WETH9 frames of X's query child and of X's transfer
child touch are fresh against WETH9's universe `UW`; the Pair rows X's transfer child touches are
fresh against `UP`. -/
structure SkimCalleeW1.XFresh (env : SkimCalleeW1 sevm b g) (weth : Adr) (UW : Weth9.Key → Prop)
    (UP : WriterKey → Prop) : Prop where
  read : StaticChildFresh sevm env.readPre fun D => Weth9.KeysFresh UW (wethRunKeys weth D)
  xWeth : CallChildFresh sevm env.xferPre fun D => Weth9.KeysFresh UW (wethRunKeys weth D)
  xPair : CallChildFresh sevm env.xferPre fun D => WriterFreshKeys UP (pairRunKeys sevm.currentTarget D)

/-- **The gas sentries of WETH9's two Skim legs (token1)**: each leg's call gas a word and room for
WETH9's run under the 63/64 rule (with the `transfer`'s `SSTORE` stipend). -/
structure SkimCalleeW1.WethSentries (env : SkimCalleeW1 sevm b g) : Prop where
  fitsRead : env.callGasQ1 < 2 ^ 256
  roomRead : balUsed sevm (afterSload sevm env.dt0 8) (skimRead1Stack sevm b env.dt0)
      ((skimRead1Base sevm b env.qd0 env.dt0).read 64 32).2 (skimRead1Ptr env.dt0) (skimT1 sevm b) ≤
    except64th (skimRead1Need sevm b env.qd0 env.dt0 env.callGasT1
        (wethBalanceSkel sevm (afterSload sevm env.dt0 8) (skimRead1Stack sevm b env.dt0)
          ((skimRead1Base sevm b env.qd0 env.dt0).read 64 32).2 (skimRead1Ptr env.dt0)
          (skimT1 sevm b)) +
      balUsed sevm (afterSload sevm env.dt0 8) (skimRead1Stack sevm b env.dt0)
        ((skimRead1Base sevm b env.qd0 env.dt0).read 64 32).2 (skimRead1Ptr env.dt0) (skimT1 sevm b))
  fitsLeg : env.callGasT1 < 2 ^ 256
  roomLeg : skimLeg1Used sevm b env.qd0 env.dt0 env.qd1 + gCallStipend ≤
    except64th (skimLeg1Need sevm b env.qd0 env.dt0 env.qd1 g +
      skimLeg1Used sevm b env.qd0 env.dt0 env.qd1)

end W1

theorem skimCachedWorld_bal (sevm : Sevm) (pre : Devm) : BalKeeps pre (skimCachedWorld sevm pre) := by
  unfold skimCachedWorld syncLockedWorld
  exact ((((BalKeeps.afterSload sevm pre 12).trans (BalKeeps.afterSstore sevm _ 12 0)).trans
    (BalKeeps.afterSload sevm _ 6)).trans (BalKeeps.afterSload sevm _ 7)).trans
    (BalKeeps.afterSload sevm _ 8)

/-- **C4(b), the skim liveness row with WETH9 as token1.**  As `pair_history_skim_live`, from the
joint checkpoint, with WETH9's query and transfer records removed (pinned in order by
`callee.gasT1`, `callee.read` and `callee.leg` to `skimLeg1Gas`, `skimWethRead1` and
`skimWethLeg1`).  The transfer's balance condition comes from C3 and the derived fact that X's
transfer leaves the locked Pair's reserve1.  What stays is X = token0's records, the lock sentries,
the first transfer's trace-local HASH-T, HASH-T over X's children, the frame's call depth and
mutability, and the legs' gas sentries. -/
theorem pair_weth9_history_skim_live_one {pair weth : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : Key → Prop} {KP : WriterKey → Prop}
    {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (joint : JointCheckpoint pair weth K₀ KP st₀ .one checkpoint.state)
    (pairFresh : WriterFreshKeys KP (pairHistoryTouchedKeys pair trace))
    (wethFresh : KeysFresh K₀ (historyTouchedKeys weth trace))
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
    (static : sevm.isStatic = false) (depth : sevm.depth ≠ 0)
    (callee : SkimCalleeW1 sevm pre g) (sentries : callee.WethSentries)
    (firstFresh : callee.FirstCallFresh (pairHistoryUniverse pair trace KP))
    (xFresh : callee.XFresh weth (historyKeyUniverse weth trace K₀)
      (pairHistoryUniverse pair trace KP)) :
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
  obtain ⟨-, -, -, -, -, noAllow⟩ := pair_weth9_joint .one trace joint pairFresh
    wethFresh factoryInstalled factoryNotSystem
  obtain ⟨futureCode, finish, K', replayed⟩ := pair_history_replayed trace joint.pairCode
    joint.pairRep pairFresh
  obtain ⟨-, tokens⟩ := replayed.fixed joint.unlocked
    (UniswapV2FactoryQuiet.pair_history_factoryQuiet trace joint.pairCode factoryInstalled
      joint.pairNonzero factoryNotSystem)
  obtain ⟨-, sumFuture, footFuture⟩ := Blanc.Lift.Weth9.weth9_history_footprint_universe
    trace joint.wethCode joint.sumNof joint.wethFoot wethFresh
  have hist : WriterRep (pairHistoryUniverse pair trace KP) (checkpoint.state.getStor pair) st₀ :=
    joint.pairRep.extend pairFresh
  obtain ⟨rep, inside⟩ := replayed.at_frame target state
  obtain ⟨code, token, -, reserve⟩ := pair_weth9_frame .one trace joint pairFresh wethFresh
    factoryInstalled factoryNotSystem state
  have ne : sevm.currentTarget ≠ weth := target ▸ joint.apart
  have np : sevm.benvStat.rules.isPrecomp weth = false :=
    propext ⟨fun h => absurd h (joint.wethNotPrecompile _ fork), fun h => absurd h Bool.false_ne_true⟩
  have tok1 : (skimToken1 sevm pre).toAdr = weth := by
    unfold skimToken1
    rw [toAdr_toB256]
    change ((Devm.getStor (afterSload sevm (syncLockedWorld sevm pre) 6)
      sevm.currentTarget).get 7).toAdr = weth
    rw [afterSload_getStor]
    change ((syncLockedWorld sevm pre).getStorVal sevm.currentTarget 7).toAdr = weth
    rw [syncLockedWorld_slot (by decide), target]
    exact token
  have tok0 : (skimToken0 sevm pre).toAdr ≠ weth := by
    unfold skimToken0
    rw [toAdr_toB256, syncLockedWorld_slot (by decide)]
    obtain ⟨-, -, -, slot6, -⟩ := rep.fixed
    change ((pre.getStor sevm.currentTarget).get 6).toAdr ≠ weth
    have token1 : st₀.token1 = weth := joint.token
    rw [slot6, tokens.1, ← token1]
    exact joint.distinct
  -- WETH9's footprint from the history's end to X's query result
  have fPre : WethFootAt weth (historyKeyUniverse weth trace K₀) pre :=
    ⟨code, by rw [state]; exact footFuture, by rw [state]; exact sumFuture⟩
  have keepsC : WethKeeps weth pre (temporalAccountAccessBase (skimCachedWorld sevm pre)
      (skimToken0 sevm pre).toAdr) :=
    (skimCachedWorld_keeps sevm pre ne).trans (WethKeeps.access _ _)
  have balC : BalKeeps pre (temporalAccountAccessBase (skimCachedWorld sevm pre)
      (skimToken0 sevm pre).toAdr) :=
    (skimCachedWorld_bal sevm pre).trans (BalKeeps.access _ _)
  have fR : WethFootAt weth (historyKeyUniverse weth trace K₀) callee.readPre :=
    (fPre.keeps keepsC balC).keeps (WethKeeps.ofSt _ _ _ _) (BalKeeps.ofSt _ _ _ _)
  have fQ := fR.static callee.qenv0.call fork ne (fun g c rest h => by
    simp only [SkimCalleeW1.readPre, St, Devm.setMach_stack, List.cons.injEq] at h
    rw [← h.2.1]
    exact tok0) xFresh.read
  have keepsQ : WethKeeps weth pre callee.qd0 :=
    keepsC.trans (WethKeeps.staticcall fork callee.qenv0.call
      (weth9_code_toList_ne (keepsC.1.trans code)))
  -- the Pair at X's query result: locked representation and code
  have world : ∀ a, Devm.getStor callee.qd0 a = Devm.getStor (syncLockedWorld sevm pre) a :=
    skimQuery_world fork callee.qenv0.call
  have repQ : WriterRep K' (callee.qd0.state.getStor sevm.currentTarget)
      { finish with unlocked := 0 } := by
    change WriterRep K' (Devm.getStor callee.qd0 sevm.currentTarget) _
    rw [world]
    unfold syncLockedWorld
    rw [afterSstore_getStor_self, afterSload_getStor]
    exact rep.mint_lock_store
  have codeQ : ∀ a, (pre.state.getCode a).toList ≠ [] →
      callee.qd0.state.getCode a = pre.state.getCode a := by
    intro a nonempty
    have c0 : callee.readPre.state.getCode a = pre.state.getCode a := by
      rw [SkimCalleeW1.readPre, St, Devm.setMach_state]
      exact balC.2 a
    exact (runCompiled_codePreserve callee.qenv0.call a
      (show (callee.readPre.state.getCode a).toList ≠ [] by rw [c0]; exact nonempty)).trans c0
  have pairPre : pre.state.getCode sevm.currentTarget = UniswapV2Pair.code := by
    rw [state, target]
    exact futureCode
  have factoryPreF : pre.state.getCode st₀.factory = UniswapV2Factory.code := by
    rw [state]
    exact UniswapV2Factory.code_eq_of_toList (history_code_of_image trace factoryInstalled)
  have pairQ : callee.qd0.state.getCode sevm.currentTarget = UniswapV2Pair.code := by
    rw [codeQ _ (by rw [pairPre]; exact UniswapV2Pair.pairSem.ne_nil rfl), pairPre]
  have factoryQ : callee.qd0.state.getCode ({ finish with unlocked := 0 } :
      UniswapV2Pair.State).factory = UniswapV2Factory.code := by
    show callee.qd0.state.getCode finish.factory = _
    rw [tokens.2.2, codeQ _ (by rw [factoryPreF]; exact UniswapV2Factory.factorySem.ne_nil rfl),
      factoryPreF]
  have zeroQ : ∀ g', Weth9Token.weth9Book.allow (Weth9.ledger (historyKeyUniverse weth trace K₀)
      (callee.qd0.state.getStor weth)) sevm.currentTarget g' = 0 := by
    intro g'
    have storQ : callee.qd0.state.getStor weth = future.state.getStor weth := by
      rw [← state]
      exact keepsQ.2
    rw [storQ, target]
    show (Weth9.trackedAllow _ _ pair g').toNat = 0
    by_cases h : historyKeyUniverse weth trace K₀ (.allow pair g')
    · rw [Weth9.trackedAllow_self h, noAllow g' h]
      rfl
    · rw [Weth9.trackedAllow_of_not h]
      rfl
  -- the reserve1 word after X's transfer is covered
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    change some (pre.state.getCode sevm.currentTarget).toList = pairSem.image
    rw [pairPre]
    rfl
  have keep1 := skimFirstCall_reserve1 (current := ⟨finish, [], []⟩) callee rep hist.inj
    hist.apart inside pairSem pairSem_image installedPre fork static firstFresh
  have cover : skimReserve1Word (callee.dt0.getStorVal sevm.currentTarget 8) ≤
      callee.qd0.getStorVal weth (Weth9.balSlot sevm.currentTarget) := by
    rw [skimReserve1Word_eq, keep1, keepsQ.getStorVal]
    change reserve1Read ((Devm.getStor callee.qd0 sevm.currentTarget).get 8) ≤ _
    rw [world]
    change reserve1Read ((syncLockedWorld sevm pre).getStorVal sevm.currentTarget 8) ≤ _
    rw [syncLockedWorld_slot (by decide), B256.le_iff_toNat_le_toNat, target]
    exact reserve
  -- WETH9's query and transfer after X's transfer
  have readFst : (skimWethRead1 sevm pre callee.qd0 callee.dt0 callee.callGasT1).1 = callee.qd1 :=
    (congrArg Prod.fst callee.read).symm
  have readSnd : (skimWethRead1 sevm pre callee.qd0 callee.dt0 callee.callGasT1).2 =
      callee.callGasQ1 := (congrArg Prod.snd callee.read).symm
  have legSnd : (skimWethLeg1 sevm pre callee.qd0 callee.dt0
      (skimWethRead1 sevm pre callee.qd0 callee.dt0 callee.callGasT1).1 g).2 = callee.callGasT1 := by
    rw [skimWethLeg1_read, callee.gasT1]
    rfl
  have legs := skimWethLeg1_of_read (callGasT1 := callee.callGasT1) (g := g)
    (U := historyKeyUniverse weth trace K₀) (stL := { finish with unlocked := 0 }) fork static depth
    callee.tenv0 tok1 tok0 ne fQ.code fQ.foot (by rw [target]; exact Or.inl joint.tracked) zeroQ
    pairQ repQ (by show (0 : B256) ≠ 1; decide) factoryQ (by rw [target]; exact joint.pairNonzero)
    fQ.bound cover xFresh.xWeth
    (fun {_ _ _ _} spawn enter child =>
      freshKeys_of_wider hist.inj hist.apart inside (xFresh.xPair spawn enter child))
    np (by rw [readSnd]; exact sentries.fitsRead) sentries.roomRead
    (by rw [legSnd]; exact sentries.fitsLeg) (by rw [readFst]; exact sentries.roomLeg)
  rw [legSnd, readFst, readSnd, ← callee.leg] at legs
  obtain ⟨⟨code1, qenv1⟩, tenv1⟩ := legs
  exact pair_history_skim_live trace joint.pairCode joint.pairRep pairFresh target state codeEq
    fork output representable value size abi selector (callee.toEnv code1 qenv1 tenv1) firstFresh

/-! ## Non-vacuity of the pins -/

/-- **The token1 skim row's pins are solvable (A17).**  For any free values (X's query result `qd0`,
X's transfer result `dt0`, the residual `g`), values of the pinned fields satisfying `gasT1`, `read`
and `leg` exist: `gasT1` reads only free values, `read` reads `gasT1`'s value, `leg` reads `read`'s
result.  And the transfer leg at the pinned query result needs exactly the pinned call gas
(`skimWethLeg1_read`), so the query's residual and the transfer's call gas agree. -/
theorem skimCalleeW1_pins_solvable (sevm : Sevm) (b qd0 dt0 : Devm) (g : Nat) :
    ∃ (callGasT1 : Nat) (qd1 : Devm) (callGasQ1 : Nat) (dt1 : Devm),
      callGasT1 = skimLeg1Gas sevm b qd0 dt0 g ∧
      (qd1, callGasQ1) = skimWethRead1 sevm b qd0 dt0 callGasT1 ∧
      dt1 = (skimWethLeg1 sevm b qd0 dt0 qd1 g).1 ∧
      (skimWethLeg1 sevm b qd0 dt0 qd1 g).2 = callGasT1 :=
  ⟨skimLeg1Gas sevm b qd0 dt0 g, (skimWethRead1 sevm b qd0 dt0 (skimLeg1Gas sevm b qd0 dt0 g)).1,
    _, _, rfl, rfl, rfl,
    congrArg Prod.snd (skimWethLeg1_read sevm b qd0 dt0 (skimLeg1Gas sevm b qd0 dt0 g) g)⟩

end Blanc.Composition.UniswapV2PairWeth9Joint
