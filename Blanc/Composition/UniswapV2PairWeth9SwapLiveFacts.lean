import Blanc.Composition.UniswapV2PairWeth9SwapLegs
import Blanc.Composition.UniswapV2PairWeth9LegsSwap0Read
import Blanc.Composition.UniswapV2PairWeth9LegsSwap0
import Blanc.Composition.UniswapV2PairWeth9Joint
import Blanc.Lift.UniswapV2Pair.PairHistoryLive
import Blanc.StorageAccessGas

/-!
# Frame facts for the history-level swap rows with WETH9 legs (C4(b), U8a2)

Shared by `pair_weth9_history_swap_live_one` and `pair_weth9_history_swap_live_zero`:

* `swap_live_of_replayed`: the body of `pair_history_swap_live` over a given replay (so the swap
  rows can use the replay `pair_weth9_joint` names, whose end conjunct bounds the reserve);
* code identity through the swap frame's own crossings (`runCompiled_codePreserve`): WETH9's code at
  the prefix world is still there at every later world of the frame, whatever the callees do;
* `depth_of_balanceEnv`: a successful `STATICCALL` record leaves call depth;
* the swap prefix world changes only the Pair's own storage;
* WETH9's charges are bounded (`xferUsed_le`, `balUsed_le`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.UniswapV2Pair

/-! ## The swap row over a given replay -/

/-- **`pair_history_swap_live`'s body over a given replay.**  The Pair's history replay, its
future code, and the swap's callee environments give the gas-exact pc-zero run and its admitted
outcome. -/
theorem swap_live_of_replayed {pair : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ finish : UniswapV2Pair.State} {K' : WriterKey → Prop}
    {trace : ConfiguredHistoryTrace cfg checkpoint future}
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (futureCode : future.state.getCode pair = UniswapV2Pair.code)
    (replayed : PairHistoryReplayed pair trace K₀ st₀ finish K')
    {sevm : Sevm} {pre : Devm}
    (target : sevm.currentTarget = pair) (state : pre.state = future.state)
    (codeEq : sevm.code = UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (output : pre.output = []) (representable : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm)
    {d0 d1 dC : Devm} {cg0 cg1 cgC g : Nat}
    (callee : SwapBackCalleeEnv sevm (swapFrontCutWorld sevm pre d0 d1 dC)
      (swapFrontCutMem sevm d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC).size
      (swapFrontPtr sevm d0 d1) (swapCutWords sevm finish) 0x257 [0x022c0d9f] (g + 1))
    (front : SwapFrontForwardEnv sevm pre finish d0 d1 dC cg0 cg1 cgC callee.gas)
    (context : SwapContextConditions (writerContext sevm []))
    (conditions : SwapModelConditions finish (swapAmount0Out sevm) (swapAmount1Out sevm)
      (swapRecipient sevm) (swapBalanceWord callee.d0.returnData)
      (swapBalanceWord callee.d1.returnData)) :
    ∃ run : Exec 0 sevm (St pre [] Mem.empty
        (swapFrontTransferGas sevm pre d0 d1 cg0 cg1 cgC callee.gas +
          swapPrefixGas sevm pre (swapAmount0Out sevm) + 279 + 166))
        (.ok (St callee.post [0x022c0d9f] callee.memory g)),
      (WriterFreshKeys (pairHistoryUniverse pair trace K₀)
          (pairDerivKeys ⟨0, sevm, _, .ok _, run⟩) →
        PairAdmittedOutcome
          (WriterExtend (pairHistoryUniverse pair trace K₀)
            (pairDerivKeys ⟨0, sevm, _, .ok _, run⟩))
          { state := finish, logs := [], updates := [] } [] K'
          ⟨0, sevm, _, .ok _, run⟩
          (St callee.post [0x022c0d9f] callee.memory g)) := by
  obtain ⟨rep, _⟩ := replayed.at_frame target state
  have nonstatic : sevm.isStatic = false := context.2
  obtain ⟨back, backGas, backPost, backMemory⟩ := callee.accepted conditions nonstatic
  obtain ⟨unlocked, positive, liquidity0, liquidity1, to0, to1, _⟩ := conditions
  have installedPre : some (pre.getCode sevm.currentTarget).toList = pairSem.image := by
    rw [target]
    change some (pre.state.getCode pair).toList = pairSem.image
    rw [state, futureCode]
    rfl
  have nonzero : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0 := by
    rcases positive with h | h
    · exact Or.inl (ne_of_gt h)
    · exact Or.inr (ne_of_gt h)
  rw [← backGas] at front ⊢
  rw [← backPost, ← backMemory]
  obtain ⟨run, _⟩ := swap_bytecode_forward_consumes
    (current := { state := finish, logs := [], updates := [] }) [] rep pairSem pairSem_image
    installedPre output codeEq fork value size selector guards unlocked nonstatic nonzero
    liquidity0 liquidity1 to0 to1 back front
  exact ⟨run, fun newFresh => pair_live_outcome initial fresh futureCode replayed run target
    state codeEq fork output representable newFresh⟩

/-! ## Code identity through the frame's crossings -/

/-- Any successful compiled step keeps every nonempty code. -/
theorem runCompiled_codePreserve {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.RunCompiled sevm pre n post) : Devm.CodePreserve pre post := by
  obtain ⟨xl, filled, run⟩ := run
  exact Ninst.effect_of_effectRec codePreserve_refl_trans.1 codePreserve_refl_trans.2
    Ninst.codePreserve_effectRec Jinst.codePreserve_effect Linst.codePreserve_effect n
    ⟨xl, filled, 0, run 0⟩

/-- WETH9's code survives a successful compiled step from a staged state over `b`. -/
theorem weth9Code_of_runCompiled {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    {n : Ninst} {a : Adr} (run : Ninst.RunCompiled sevm (St b S M G) n d)
    (code : b.state.getCode a = Weth9.code) : d.state.getCode a = Weth9.code := by
  have nonempty : ((St b S M G).getCode a).toList ≠ [] := by
    change (b.state.getCode a).toList ≠ []
    rw [code]
    exact Blanc.Lift.Weth9.weth9Sem.ne_nil rfl
  change d.getCode a = Weth9.code
  rw [runCompiled_codePreserve run a nonempty]
  exact code

/-- WETH9's code survives warming an address. -/
theorem weth9Code_temporal {b : Devm} {t a : Adr} (code : b.state.getCode a = Weth9.code) :
    (temporalAccountAccessBase b t).state.getCode a = Weth9.code := by
  rw [temporalAccountAccessBase_state]
  exact code

/-! ## Call depth from a successful `STATICCALL` record -/

/-- A successful post-callback `balanceOf` record leaves call depth: at depth zero the
`STATICCALL` pushes the failure flag. -/
theorem depth_of_balanceEnv {sevm : Sevm} {b : Devm} {M : Mem} {p t : B256} {S : List B256}
    {d : Devm} {callGas tailGas : Nat} (fork : CoveredFork sevm.benvStat.fork)
    (env : SwapBalanceEnv sevm b M p t S d callGas tailGas) : sevm.depth ≠ 0 := by
  obtain ⟨xl, filled, run⟩ := env.call
  have hp : (callGas.toB256 :: swapTokenWord t :: p :: 36 :: p :: 32 ::
      ((p + 36) :: 0x70a08231 :: swapTokenWord t :: S)) <<+
      (St (temporalAccountAccessBase b (swapTokenWord t).toAdr)
        (callGas.toB256 :: swapTokenWord t :: p :: 36 :: p :: 32 :: (p + 36) :: 0x70a08231 ::
          swapTokenWord t :: S) (swapBalanceRequest M p sevm.currentTarget) callGas).stack := by
    simpa only [List.append_nil, St.stack] using
      (pref_append (callGas.toB256 :: swapTokenWord t :: p :: 36 :: p :: 32 ::
        ((p + 36) :: 0x70a08231 :: swapTokenWord t :: S)) [])
  rcases of_run_staticcall_val_with_depth_cause hp ⟨xl, filled, 0, run 0⟩ fork with
    ⟨flag, -⟩ | ⟨_, _, _, _, _, _, _, depth, -⟩
  · rw [env.success] at flag
    exact absurd (pref_head_unique flag (pref_append [(1 : B256)] _)) (by decide)
  · exact Nat.pos_iff_ne_zero.mp depth

/-! ## The swap prefix world -/

theorem afterSload_state (sevm : Sevm) (b : Devm) (k : B256) :
    (afterSload sevm b k).state = b.state := by
  unfold afterSload
  split <;> rfl

theorem setStorVal_state_getCode (d : Devm) (adr : Adr) (k v : B256) (a : Adr) :
    (d.setStorVal adr k v).state.getCode a = d.state.getCode a := by
  show ((d.state.setStorVal adr k v).get a).code = (d.state.get a).code
  unfold State.setStorVal
  by_cases h : adr = a
  · subst h
    rw [State.get_set_self]
  · rw [State.get_set_ne _ h]

theorem afterSstore_getCode (sevm : Sevm) (b : Devm) (k v : B256) (a : Adr) :
    (afterSstore sevm b k v).state.getCode a = b.state.getCode a := by
  unfold afterSstore
  split <;> exact setStorVal_state_getCode _ _ _ _ _

/-- The prefix world keeps every code. -/
theorem swapPrefixWorld_getCode (sevm : Sevm) (b : Devm) (a : Adr) :
    (swapPrefixWorld sevm b).state.getCode a = b.state.getCode a := by
  unfold swapPrefixWorld mintLockedWorld
  rw [afterSload_state, afterSload_state, afterSload_state, afterSstore_getCode, afterSload_state]

/-- The prefix world keeps every storage word off the Pair. -/
theorem swapPrefixWorld_getStorVal (sevm : Sevm) (b : Devm) {a : Adr}
    (ne : a ≠ sevm.currentTarget) (k : B256) :
    (swapPrefixWorld sevm b).getStorVal a k = b.getStorVal a k := by
  have stor : Devm.getStor (swapPrefixWorld sevm b) a = Devm.getStor b a := by
    unfold swapPrefixWorld mintLockedWorld
    rw [afterSload_getStor, afterSload_getStor, afterSload_getStor,
      afterSstore_getStor_ne _ _ _ _ _ (Ne.symm ne), afterSload_getStor]
  change (Devm.getStor (swapPrefixWorld sevm b) a).get k = (Devm.getStor b a).get k
  rw [stor]

/-! ## WETH9's charges are bounded -/

theorem xferUsed_le (sevm : Sevm) (W : Devm) (L : List B256) (M : Mem)
    (p amount toWord token rho : B256) :
    xferUsed sevm W L M p amount toWord token rho ≤ 53262 := by
  unfold xferUsed xferUsedAt Weth9.transferGas Weth9.xferGasSelf Weth9.xfTailGas
  generalize initSevm _ = s
  generalize initDevm _ = d
  have bound : ∀ (b : Devm) (k v : B256), sstoreCost s b k v ≤ 22100 := fun b k v =>
    Nat.le_trans (sstoreCost_le_value s b k v)
      (Nat.add_le_add_left (sstoreValueCost_le _ _ _) _)
  have l1 := sloadCost_le s
  have := bound (Weth9.tT3 s (Weth9.pB1 s d s.caller) s.caller (Sevm.dataWord s 4).toAdr
    (Sevm.dataWord s 36)) (Weth9.balSlot (Sevm.dataWord s 4).toAdr)
    (Weth9.tV2 s (Weth9.pB1 s d s.caller) s.caller (Sevm.dataWord s 4).toAdr (Sevm.dataWord s 36))
  have := bound (Weth9.tT1 s (Weth9.pB1 s d s.caller) s.caller) (Weth9.balSlot s.caller)
    (Weth9.tV1 s (Weth9.pB1 s d s.caller) s.caller (Sevm.dataWord s 36))
  have := l1 (Weth9.tT2 s (Weth9.pB1 s d s.caller) s.caller (Sevm.dataWord s 36))
    (Weth9.balSlot (Sevm.dataWord s 4).toAdr)
  have := l1 (Weth9.pB1 s d s.caller) (Weth9.balSlot s.caller)
  have := l1 d (Weth9.balSlot s.caller)
  simp only [gasColdSload] at *
  omega

theorem balUsed_le (sevm : Sevm) (B : Devm) (S : List B256) (M : Mem) (p t : B256) :
    balUsed sevm B S M p t ≤ 2534 := by
  unfold balUsed weth9BalanceGas
  split <;> omega

/-! ## The back half reads its world only off non-gas fields

A WETH9 leg's result differs across call gases only in its gas column, so the join world a callee
environment is built over may be taken on the leg's gas-free skeleton.  The post-callback
`balanceOf` record and the request staging charge read that world only off non-gas fields. -/

theorem withGasLeft_self (d : Devm) : d.withGasLeft d.gasLeft = d := rfl

/-- The request staging charge reads the world only off its warm set. -/
theorem swapRequestCharge_withGasLeft (b : Devm) (x n : Nat) (p t : B256) (fixed : Nat) :
    swapRequestCharge (b.withGasLeft x) n p t fixed = swapRequestCharge b n p t fixed := rfl

/-- Account warming commutes with a gas shift. -/
theorem temporalAccountAccessBase_withGasLeft (b : Devm) (x : Nat) (a : Adr) :
    temporalAccountAccessBase (b.withGasLeft x) a = (temporalAccountAccessBase b a).withGasLeft x := by
  unfold temporalAccountAccessBase
  rw [withGasLeft_accessedAddresses]
  by_cases h : a ∈ b.accessedAddresses
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

theorem St_temporal_withGasLeft (b : Devm) (x : Nat) (a : Adr) (S : List B256) (M : Mem) (G : Nat) :
    St (temporalAccountAccessBase (b.withGasLeft x) a) S M G = St (temporalAccountAccessBase b a) S M G := by
  rw [temporalAccountAccessBase_withGasLeft]
  rfl

/-- A `balanceOf` record reads its world only off non-gas fields. -/
theorem swapBalanceEnv_withGasLeft {sevm : Sevm} {b : Devm} {M : Mem} {p t : B256} {S : List B256}
    {d : Devm} {callGas tailGas : Nat} (x : Nat) (env : SwapBalanceEnv sevm b M p t S d callGas tailGas) :
    SwapBalanceEnv sevm (b.withGasLeft x) M p t S d callGas tailGas :=
  ⟨env.code, by rw [St_temporal_withGasLeft]; exact env.call, env.success, env.long, env.returnedGas⟩

/-- The join world over a gas-shifted transfer result is the gas-shifted join world. -/
theorem swapFrontCutWorld_withGasLeft (sevm : Sevm) (b d0 d dC : Devm) (x : Nat) :
    ∃ y, swapFrontCutWorld sevm b d0 (d.withGasLeft x) dC =
      (swapFrontCutWorld sevm b d0 d dC).withGasLeft y := by
  unfold swapFrontCutWorld swapFrontTransferWorld swapOptWorld
  by_cases e : swapDataLength sevm = 0
  · by_cases a1 : swapAmount1Out sevm = 0
    · simp only [e, a1, ↓reduceIte]
      exact ⟨_, (withGasLeft_self _).symm⟩
    · simp only [e, a1, ↓reduceIte]
      exact ⟨x, rfl⟩
  · simp only [e, ↓reduceIte]
    exact ⟨_, (withGasLeft_self _).symm⟩

/-- The same with the first transfer's result gas-shifted (WETH9 = token0). -/
theorem swapFrontCutWorld_withGasLeft0 (sevm : Sevm) (b d d1 dC : Devm) (x : Nat) :
    ∃ y, swapFrontCutWorld sevm b (d.withGasLeft x) d1 dC =
      (swapFrontCutWorld sevm b d d1 dC).withGasLeft y := by
  unfold swapFrontCutWorld swapFrontTransferWorld swapOptWorld
  by_cases e : swapDataLength sevm = 0
  · by_cases a1 : swapAmount1Out sevm = 0
    · by_cases a0 : swapAmount0Out sevm = 0
      · simp only [e, a1, a0, ↓reduceIte]
        exact ⟨_, (withGasLeft_self _).symm⟩
      · simp only [e, a1, a0, ↓reduceIte]
        exact ⟨x, rfl⟩
    · simp only [e, a1, ↓reduceIte]
      exact ⟨_, (withGasLeft_self _).symm⟩
  · simp only [e, ↓reduceIte]
    exact ⟨_, (withGasLeft_self _).symm⟩

theorem swapFrontCutMem_withGasLeft (sevm : Sevm) (d0 d dC : Devm) (x : Nat) :
    swapFrontCutMem sevm d0 (d.withGasLeft x) dC = swapFrontCutMem sevm d0 d dC := rfl

theorem swapFrontCutMem_withGasLeft0 (sevm : Sevm) (d d1 dC : Devm) (x : Nat) :
    swapFrontCutMem sevm (d.withGasLeft x) d1 dC = swapFrontCutMem sevm d d1 dC := rfl

theorem swapFrontPtr_withGasLeft (sevm : Sevm) (d0 d : Devm) (x : Nat) :
    swapFrontPtr sevm d0 (d.withGasLeft x) = swapFrontPtr sevm d0 d := rfl

theorem swapFrontPtr_withGasLeft0 (sevm : Sevm) (d d1 : Devm) (x : Nat) :
    swapFrontPtr sevm (d.withGasLeft x) d1 = swapFrontPtr sevm d d1 := rfl

section ReadGasFree

variable (sevm : Sevm) (B : Devm) (x : Nat) (S : List B256) (M : Mem) (p t : B256)

theorem balPopped_withGasLeft (g : Nat) :
    balPopped sevm (B.withGasLeft x) S M p t g = balPopped sevm B S M p t g := by
  unfold balPopped
  rw [temporalAccountAccessBase_withGasLeft]
  rfl

theorem balAcc_withGasLeft : balAcc (B.withGasLeft x) t = balAcc B t := by
  unfold balAcc
  rw [temporalAccountAccessBase_withGasLeft]
  rfl

theorem balExt_withGasLeft : balExt sevm (B.withGasLeft x) S M p t = balExt sevm B S M p t := by
  unfold balExt
  rw [balPopped_withGasLeft]

theorem balParent_withGasLeft (g k : Nat) :
    balParent sevm (B.withGasLeft x) S M p t g k = balParent sevm B S M p t g k := by
  unfold balParent balWarm
  rw [balPopped_withGasLeft]

theorem balMsg_withGasLeft (g k f : Nat) :
    balMsg sevm (B.withGasLeft x) S M p t g k f = balMsg sevm B S M p t g k f := by
  unfold balMsg
  rw [balParent_withGasLeft]
  rfl

theorem balUsed_withGasLeft : balUsed sevm (B.withGasLeft x) S M p t = balUsed sevm B S M p t := by
  unfold balUsed
  rw [balMsg_withGasLeft]

theorem wethBalanceSkel_withGasLeft :
    wethBalanceSkel sevm (B.withGasLeft x) S M p t = wethBalanceSkel sevm B S M p t := by
  unfold wethBalanceSkel
  rw [balParent_withGasLeft, balMsg_withGasLeft]

theorem wethBalanceCall_withGasLeft (cg : Nat) :
    wethBalanceCall sevm (B.withGasLeft x) S M p t cg = wethBalanceCall sevm B S M p t cg := by
  unfold wethBalanceCall wethBalanceCallAt balSplit
  rw [balParent_withGasLeft, balMsg_withGasLeft, balExt_withGasLeft, balAcc_withGasLeft,
    balUsed_withGasLeft]

theorem wethReadLeg_withGasLeft (need : Devm → Nat) :
    wethReadLeg sevm (B.withGasLeft x) S M p t need = wethReadLeg sevm B S M p t need := by
  unfold wethReadLeg readLegGas
  rw [wethBalanceCall_withGasLeft, wethBalanceSkel_withGasLeft, balAcc_withGasLeft,
    balExt_withGasLeft, balUsed_withGasLeft]

end ReadGasFree

/-- The WETH9 first query (WETH9 = token0) reads its join world only off non-gas fields. -/
theorem swapWethRead0_withGasLeft (sevm : Sevm) (d : Devm) (x : Nat) (M : Mem) (n : Nat) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (callGas1 : Nat) :
    swapWethRead0 sevm (d.withGasLeft x) M n p w ρ R callGas1 =
      swapWethRead0 sevm d M n p w ρ R callGas1 :=
  wethReadLeg_withGasLeft _ _ _ _ _ _ _ _

end Blanc.Composition.UniswapV2PairWeth9Joint
