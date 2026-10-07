import Blanc.Lift.UniswapV2Pair.Creation.Deploy
import Blanc.Lift.UniswapV2Pair.InitializeSource

/-!
# Deploy, then `initialize`: the initialized checkpoint

`InitializedCheckpoint` is the proposed U2 checkpoint predicate: the pair's raw storage represents,
with the empty tracked footprint (`WriterRep (fun _ => False)`), the model state `State.empty`
(`Model.lean`) of a pair created by `factory` with domain separator `domain`, after
`initialize(token0, token1)`.  Read out, it says: zero supply, reserves, timestamp, accumulators
and `kLast`; `unlocked = 1`; `factory`, `token0`, `token1` and the domain separator as given; no
other nonzero word than at a fixed slot; every ledger, allowance and nonce row zero in the model.
It is no claim that every hashed mapping slot reads zero: with the empty footprint a future touch
introduces its own trace-local freshness (HASH-T), exactly as the WETH9 deployment checkpoint.

* `ctorStor_rep`: the constructor's storage represents `State.empty factory domain`;
* `pair_initialized`: a successful `initialize` frame at a pair whose storage is the constructor's
  storage, called by the factory, leaves storage satisfying the checkpoint predicate;
* `pair_create2_initialized`: `pair_create2` composed with it, for any covered fork;
* `exhibit_create2`: the exhibit USDC/WETH instance, whose address is `pairAddress`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The model state after `factory` deploys a pair with domain separator `domain` and initializes
it with `token0`, `token1`. -/
def initializedState (factory : Adr) (domain : B256) (token0 token1 : Adr) : State :=
  initializeSourceState (State.empty factory domain) token0 token1

/-- **The initialized checkpoint** (proposed U2 checkpoint predicate): the empty tracked
footprint represents `initializedState`. -/
def InitializedCheckpoint (s : Stor) (factory : Adr) (domain : B256) (token0 token1 : Adr) :
    Prop :=
  WriterRep (fun _ => False) s (initializedState factory domain token0 token1)

end Blanc.Lift.UniswapV2Pair

namespace Blanc.Lift.UniswapV2Pair.Creation

open Jaune Blanc.Lift

/-- The constructor's storage represents the empty model state with the empty footprint. -/
theorem ctorStor_rep (chainWord : B256) (self factory : Adr) :
    WriterRep (fun _ => False) (ctorStor chainWord self factory Stor.empty)
      (State.empty factory (domainSeparator chainWord self)) := by
  have get : ∀ n : B256, (ctorStor chainWord self factory Stor.empty).get n =
      if (5 : B256) = n then factory.toB256 else if (3 : B256) = n then
        domainSeparator chainWord self else if (12 : B256) = n then 1 else 0 := by
    intro n
    unfold ctorStor
    rw [Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite]
    rfl
  have off : ∀ n : B256, n ≠ 3 → n ≠ 5 → n ≠ 12 →
      (ctorStor chainWord self factory Stor.empty).get n = 0 := by
    intro n h3 h5 h12
    rw [get, ite_eq_right (Ne.symm h5), ite_eq_right (Ne.symm h3), ite_eq_right (Ne.symm h12)]
  refine ⟨⟨[], fun _ => ⟨False.elim, fun h => nomatch h⟩⟩, ?_, ?_,
    fun _ _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, ?_⟩
  · refine ⟨off 0 (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [get, ite_eq_right (by decide), ite_eq_left rfl]
      rfl
    · rw [get, ite_eq_left rfl, toAdr_toB256]
      rfl
    · rw [off 6 (by decide) (by decide) (by decide)]
      rfl
    · rw [off 7 (by decide) (by decide) (by decide)]
      rfl
    · rw [off 8 (by decide) (by decide) (by decide)]
      show reserve0Read 0 = Nat.toB256 0
      decide
    · rw [off 8 (by decide) (by decide) (by decide)]
      show reserve1Read 0 = Nat.toB256 0
      decide
    · rw [off 8 (by decide) (by decide) (by decide)]
      show reserveTimestampRead 0 = (0 : UInt32).toB256
      decide
    · rw [off 9 (by decide) (by decide) (by decide)]
      rfl
    · rw [off 10 (by decide) (by decide) (by decide)]
      rfl
    · rw [off 11 (by decide) (by decide) (by decide)]
      rfl
    · rw [get, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
      rfl
  · intro n nonzero
    refine .inl ?_
    by_cases h3 : n = 3
    · rw [h3]; decide
    · by_cases h5 : n = 5
      · rw [h5]; decide
      · by_cases h12 : n = 12
        · rw [h12]; decide
        · exact absurd (off n h3 h5 h12) nonzero
  · intro k _
    cases k <;> rfl

/-- **Initializing a freshly deployed pair.**  A successful pc-zero run of the certified runtime
on `initialize` at a pair whose storage is the constructor's storage for `factory` leaves storage
satisfying the initialized checkpoint, with the decoded `token0`, `token1`. -/
theorem pair_initialized {chainWord : B256} {factory : Adr}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (hstor : Devm.getStor b sevm.currentTarget =
      ctorStor chainWord sevm.currentTarget factory Stor.empty)
    (representable : sevm.data.length < 2 ^ 256) (freshOutput : b.output = [])
    (codeEq : sevm.code = Blanc.Lift.UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.caller = factory ∧
      InitializedCheckpoint (post.getStor sevm.currentTarget) factory
        (domainSeparator chainWord sevm.currentTarget) (initializeToken0 sevm)
        (initializeToken1 sevm) := by
  have rep := ctorStor_rep chainWord sevm.currentTarget factory
  rw [← hstor] at rep
  obtain ⟨-, -, authorized, -, residual, result⟩ :=
    initialize_bytecode_refines_source (current := ⟨State.empty factory
      (domainSeparator chainWord sevm.currentTarget), [], []⟩) (invocation := [])
      rep representable freshOutput codeEq fork selector run
  exact ⟨authorized, result.representation⟩

/-- **Deploy by `CREATE2`, then initialize**, under any covered fork: the `CREATE2` step of
`pair_create2` from the factory frame `sevm` leaves at the new address the certified runtime and
storage from which every successful `initialize` by the factory reaches the initialized
checkpoint over the creating frame's chain id and that address. -/
theorem pair_create2_initialized {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {i sz salt : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hinit : create2InitCode M i sz = code.toList)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt code.toList))
        (create2NewAddress sevm.currentTarget salt code.toList))
    (hgas : 2400000 ≤ except64th G) (hroom : S.length < 1024) :
    ∃ post, Ninst.RunCompiled sevm (St b (0 :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) (.exec .create2) post ∧
      post.stack = (create2NewAddress sevm.currentTarget salt code.toList).toB256 :: S ∧
      (post.getCode (create2NewAddress sevm.currentTarget salt code.toList)).toList =
        Blanc.Lift.UniswapV2Pair.code.toList ∧
      ∀ {isevm : Sevm} {ib ipost : Devm} {iG : Nat},
        isevm.currentTarget = create2NewAddress sevm.currentTarget salt code.toList →
        Devm.getStor ib isevm.currentTarget =
          Devm.getStor post (create2NewAddress sevm.currentTarget salt code.toList) →
        isevm.caller = sevm.currentTarget →
        isevm.data.length < 2 ^ 256 → ib.output = [] →
        isevm.code = Blanc.Lift.UniswapV2Pair.code → CoveredFork isevm.benvStat.fork →
        Blanc.Sevm.selector isevm = 0x485cc955 →
        Exec 0 isevm (St ib [] Mem.empty iG) (.ok ipost) →
        InitializedCheckpoint (ipost.getStor isevm.currentTarget) sevm.currentTarget
          (domainSeparator sevm.benvStat.chainId.toB256
            (create2NewAddress sevm.currentTarget salt code.toList))
          (initializeToken0 isevm) (initializeToken1 isevm) := by
  obtain ⟨post, hrun, hstack, hcode, hstor⟩ :=
    pair_create2 hfork hstatic hinit hnonce hdepth hfresh hgas hroom
  refine ⟨post, hrun, hstack, hcode, ?_⟩
  intro isevm ib ipost iG htarget hpre _ representable freshOutput codeEq fork
    selector run
  have hib : Devm.getStor ib isevm.currentTarget =
      ctorStor sevm.benvStat.chainId.toB256 isevm.currentTarget sevm.currentTarget
        Stor.empty := by
    rw [hpre, hstor, htarget]
  have h := (pair_initialized hib representable freshOutput codeEq
    fork selector run).2
  rw [htarget] at h ⊢
  exact h

/-- **The exhibit pair, deployed.**  A `CREATE2` from the Uniswap V2 factory with salt
`keccak(USDC ‖ WETH)` carrying the creation code pushes the exhibit address `pairAddress` and
installs the certified runtime and constructor storage there (the factory as `factory`). -/
theorem exhibit_create2 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {i sz : B256}
    (hfactory : sevm.currentTarget = factory)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hinit : create2InitCode M i sz = code.toList)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz pairAddress) pairAddress)
    (hgas : 2400000 ≤ except64th G) (hroom : S.length < 1024) :
    ∃ post, Ninst.RunCompiled sevm (St b (0 :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) (.exec .create2) post ∧
      post.stack = pairAddress.toB256 :: S ∧
      (post.getCode pairAddress).toList = Blanc.Lift.UniswapV2Pair.code.toList ∧
      Devm.getStor post pairAddress =
        ctorStor sevm.benvStat.chainId.toB256 pairAddress factory Stor.empty := by
  have haddr : create2NewAddress sevm.currentTarget salt code.toList = pairAddress := by
    rw [hfactory, pairAddress_eq]
  rw [← haddr] at hfresh
  have h := pair_create2 hfork hstatic hinit hnonce hdepth hfresh hgas hroom
  rw [haddr, hfactory] at h
  exact h

/-! ## The `initialize` run, constructed

`pair_create2_initialized` says every successful `initialize` reaches the checkpoint; the two
results below construct that run.

* `pair_initialize_live`: at constructor storage, a factory-called `initialize` frame (zero value,
  non-static, two calldata words, gas meeting the two store sentries) has a successful run at its
  closed gas, reaching the checkpoint;
* `pair_create2_initialize_live`: `pair_create2` composed with it.
-/

/-- **Initializing a freshly deployed pair, constructed.**  At a pair whose storage is the
constructor's storage for `factory`, an `initialize` frame called by `factory` with zero value,
non-static, carrying the selector and two calldata words, whose gas meets the two store sentries,
has a successful pc-zero run of the certified runtime at its closed gas
`iG + initializeStorageCharge isevm ib + 377`, and that run leaves storage satisfying the
initialized checkpoint with the decoded `token0`, `token1`.  The authorization
`caller = slot 5` comes from the constructor storage, which holds `factory` there. -/
theorem pair_initialize_live {chainWord : B256} {factory : Adr} {isevm : Sevm} {ib : Devm}
    {iG : Nat}
    (hstor : Devm.getStor ib isevm.currentTarget =
      ctorStor chainWord isevm.currentTarget factory Stor.empty)
    (caller : isevm.caller = factory) (value : isevm.value = 0)
    (nonstatic : isevm.isStatic = false)
    (codeEq : isevm.code = Blanc.Lift.UniswapV2Pair.code)
    (fork : CoveredFork isevm.benvStat.fork)
    (selector : Blanc.Sevm.selector isevm = 0x485cc955)
    (size : (4 : B256) ≤ isevm.data.length.toB256)
    (guard : (64 : B256) ≤ isevm.data.length.toB256 - 4)
    (representable : isevm.data.length < 2 ^ 256) (freshOutput : ib.output = [])
    (sentry0 : gCallStipend < iG + initializeStore0Charge isevm ib +
      initializeLoad1Charge isevm ib + initializeStore1Charge isevm ib + 39)
    (sentry1 : gCallStipend < iG + initializeStore1Charge isevm ib + 9) :
    ∃ ipost, Nonempty (Exec 0 isevm
        (St ib [] Mem.empty (iG + initializeStorageCharge isevm ib + 377)) (.ok ipost)) ∧
      InitializedCheckpoint (ipost.getStor isevm.currentTarget) factory
        (domainSeparator chainWord isevm.currentTarget) (initializeToken0 isevm)
        (initializeToken1 isevm) := by
  have authorized : isevm.caller = (ib.getStorVal isevm.currentTarget 5).toAdr := by
    show _ = ((Devm.getStor ib isevm.currentTarget).get 5).toAdr
    rw [hstor, ctorStor, Stor.get_set_self, toAdr_toB256]
    exact caller
  obtain ⟨run⟩ := initialize_bytecode_live_raw codeEq fork value size selector guard
    authorized sentry0 sentry1 nonstatic
  exact ⟨_, ⟨run⟩, (pair_initialized hstor representable freshOutput codeEq fork selector run).2⟩

/-- **Deploy by `CREATE2`, then initialize, both constructed**, under any covered fork: the
`CREATE2` step of `pair_create2` from the factory frame `sevm` leaves at the new address the
certified runtime and storage such that every `initialize` frame at that address over that
storage, called by the factory with zero value, non-static, carrying the selector and two calldata
words and gas meeting the two store sentries, has a successful run at its closed gas reaching the
initialized checkpoint over the creating frame's chain id, that address and the decoded tokens.
`pair_create2_initialized` is the universal half: every successful run reaches it. -/
theorem pair_create2_initialize_live {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {i sz salt : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hinit : create2InitCode M i sz = code.toList)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt code.toList))
        (create2NewAddress sevm.currentTarget salt code.toList))
    (hgas : 2400000 ≤ except64th G) (hroom : S.length < 1024) :
    ∃ post, Ninst.RunCompiled sevm (St b (0 :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) (.exec .create2) post ∧
      post.stack = (create2NewAddress sevm.currentTarget salt code.toList).toB256 :: S ∧
      (post.getCode (create2NewAddress sevm.currentTarget salt code.toList)).toList =
        Blanc.Lift.UniswapV2Pair.code.toList ∧
      ∀ {isevm : Sevm} {ib : Devm} {iG : Nat},
        isevm.currentTarget = create2NewAddress sevm.currentTarget salt code.toList →
        Devm.getStor ib isevm.currentTarget =
          Devm.getStor post (create2NewAddress sevm.currentTarget salt code.toList) →
        isevm.caller = sevm.currentTarget → isevm.value = 0 → isevm.isStatic = false →
        isevm.code = Blanc.Lift.UniswapV2Pair.code → CoveredFork isevm.benvStat.fork →
        Blanc.Sevm.selector isevm = 0x485cc955 →
        (4 : B256) ≤ isevm.data.length.toB256 → (64 : B256) ≤ isevm.data.length.toB256 - 4 →
        isevm.data.length < 2 ^ 256 → ib.output = [] →
        gCallStipend < iG + initializeStore0Charge isevm ib +
          initializeLoad1Charge isevm ib + initializeStore1Charge isevm ib + 39 →
        gCallStipend < iG + initializeStore1Charge isevm ib + 9 →
        ∃ ipost, Nonempty (Exec 0 isevm
            (St ib [] Mem.empty (iG + initializeStorageCharge isevm ib + 377)) (.ok ipost)) ∧
          InitializedCheckpoint (ipost.getStor isevm.currentTarget) sevm.currentTarget
            (domainSeparator sevm.benvStat.chainId.toB256
              (create2NewAddress sevm.currentTarget salt code.toList))
            (initializeToken0 isevm) (initializeToken1 isevm) := by
  obtain ⟨post, hrun, hstack, hcode, hstor⟩ :=
    pair_create2 hfork hstatic hinit hnonce hdepth hfresh hgas hroom
  refine ⟨post, hrun, hstack, hcode, ?_⟩
  intro isevm ib iG htarget hpre caller value nonstatic codeEq fork selector size guard
    representable freshOutput sentry0 sentry1
  have hib : Devm.getStor ib isevm.currentTarget =
      ctorStor sevm.benvStat.chainId.toB256 isevm.currentTarget sevm.currentTarget
        Stor.empty := by
    rw [hpre, hstor, htarget]
  have h := pair_initialize_live hib caller value nonstatic codeEq fork selector size guard
    representable freshOutput sentry0 sentry1
  rw [htarget] at h ⊢
  exact h

end Blanc.Lift.UniswapV2Pair.Creation
