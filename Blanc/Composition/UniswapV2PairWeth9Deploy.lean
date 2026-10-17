import Blanc.Composition.UniswapV2PairWeth9Checkpoint
import Blanc.Lift.UniswapV2Pair.Creation.DeployInit
import Blanc.Lift.ExactWalkSolc
import Blanc.ForwardStorageAccess

/-!
# C5: the joint checkpoint by deployment

`pair_weth9_create2_jointCheckpoint` composes the Pair's `CREATE2` deployment and `initialize`
(`pair_create2_initialize_live`) with WETH9 world-agreement hypotheses at the `initialize` world:
the result world satisfies `JointCheckpoint` with the initialized model state and no tracked Pair
row.

The point is that the `initialize` frame touches no account but the Pair's storage
(`initialize_run_frame`): its successful run is the certified image `initializePublicPost`, three
`SLOAD`s and two `SSTORE`s at the Pair, so every account's code and balance and every other
account's storage (WETH9's in particular) are those of the `initialize` world.  The `CREATE2` frame
enters only through that world's agreement with the deployment's WETH9 storage
(`ib.state.getStor weth = b.state.getStor weth`), which carries the pre-deployment zero allowance
rows of the new address.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair

/-- **A successful `initialize` frame touches only the Pair's storage**: every account's code and
balance, and every other account's storage, are unchanged. -/
theorem initialize_run_frame {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = Blanc.Lift.UniswapV2Pair.code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x485cc955)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    (∀ a, post.getCode a = b.getCode a) ∧ (∀ a, post.getBal a = b.getBal a) ∧
      ∀ a, sevm.currentTarget ≠ a → Devm.getStor post a = Devm.getStor b a := by
  obtain ⟨-, -, -, -, -, residual, rfl⟩ := initialize_bytecode_refines_raw codeEq fork selector run
  unfold initializePublicPost initializePublicBase initializeCoreBase initializeWritesBase
    initializeLoaded1 initializeStored0 initializeLoaded0 initializeFactoryBase St
  refine ⟨fun a => ?_, fun a => ?_, fun a ha => ?_⟩
  · rw [Devm.getCode_setMach, afterSstore_getCode, afterSload_getCode, afterSstore_getCode,
      afterSload_getCode, afterSload_getCode]
  · rw [show ∀ (d : Devm) (m : Mach), (d.setMach m).getBal a = d.getBal a from fun _ _ => rfl,
      afterSstore_getBal]
    unfold Devm.getBal
    rw [afterSload_getAcct]
    change ((afterSstore sevm _ 6 _).getBal a) = _
    rw [afterSstore_getBal]
    unfold Devm.getBal
    rw [afterSload_getAcct, afterSload_getAcct]
  · rw [show ∀ (d : Devm) (m : Mach), Devm.getStor (d.setMach m) a = Devm.getStor d a from
      fun _ _ => rfl, afterSstore_getStor_ne _ _ _ _ _ ha, afterSload_getStor,
      afterSstore_getStor_ne _ _ _ _ _ ha, afterSload_getStor, afterSload_getStor]

/-- **C5: the joint checkpoint by deployment** (every covered fork).  From a world whose WETH9
satisfies its footprint invariant with the new address's balance row tracked and its allowance rows
zero (the trace-local condition that the new address has not acted as a WETH9 sender), the Pair's
`CREATE2` deployment (`pair_create2_initialize_live`) and every successful `initialize` naming WETH9 as
`token1`, at a world that agrees with the deployment's WETH9 account, give a world satisfying the
joint checkpoint with the initialized model state and no tracked Pair row.  Amended (A3/A10): the
new address is neither zero nor the system address, and `initialize` names a `token0` other than
WETH9.  Amended (A11): WETH9's address is no precompile under any covered fork. -/
theorem pair_weth9_create2_jointCheckpoint {weth : Adr} {K₀ : Key → Prop}
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {i sz salt : B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hinit : create2InitCode M i sz = UniswapV2Pair.Creation.code.toList)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hdepth : sevm.depth ≠ 0)
    (hfresh : Create2TargetEmpty (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList))
        (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList))
    (hgas : 2400000 ≤ except64th G) (hroom : S.length < 1024)
    (wethApart : weth ≠ create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList)
    (pairNonzero : create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList ≠ 0)
    (notSystem :
      create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList ≠ systemAddress)
    (tracked : K₀ (.bal (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList)))
    (noAllowance : ∀ g, K₀ (.allow (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList) g) →
      (b.state.getStor weth).get
        (allowSlot (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList) g) = 0)
    (wethNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp weth) :
    ∃ post, Ninst.RunCompiled sevm (St b (0 :: i :: sz :: salt :: S) M
        (G + create2Charge sevm M i sz)) (.exec .create2) post ∧
      post.stack = (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList).toB256 :: S ∧
      ∀ {isevm : Sevm} {ib : Devm} {iG : Nat},
        isevm.currentTarget = create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList →
        Devm.getStor ib isevm.currentTarget =
          Devm.getStor post (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList) →
        ib.state.getCode isevm.currentTarget = post.state.getCode isevm.currentTarget →
        isevm.caller = sevm.currentTarget → isevm.value = 0 → isevm.isStatic = false →
        isevm.code = Blanc.Lift.UniswapV2Pair.code → CoveredFork isevm.benvStat.fork →
        Blanc.Sevm.selector isevm = 0x485cc955 →
        (4 : B256) ≤ isevm.data.length.toB256 → (64 : B256) ≤ isevm.data.length.toB256 - 4 →
        isevm.data.length < 2 ^ 256 → ib.output = [] →
        gCallStipend < iG + initializeStore0Charge isevm ib +
          initializeLoad1Charge isevm ib + initializeStore1Charge isevm ib + 39 →
        gCallStipend < iG + initializeStore1Charge isevm ib + 9 →
        initializeToken1 isevm = weth →
        initializeToken0 isevm ≠ weth →
        some (ib.state.getCode weth).toList = weth9Sem.image →
        FootInv K₀ (ib.state.getStor weth) (ib.state.bal weth) →
        ib.state.getStor weth = b.state.getStor weth →
        SumNof ib.state.bal →
        ∃ ipost, Nonempty (Exec 0 isevm
            (St ib [] Mem.empty (iG + initializeStorageCharge isevm ib + 377)) (.ok ipost)) ∧
          JointCheckpoint isevm.currentTarget weth K₀ (fun _ => False)
            (initializedState sevm.currentTarget
              (UniswapV2Pair.Creation.domainSeparator sevm.benvStat.chainId.toB256 isevm.currentTarget)
              (initializeToken0 isevm) weth) .one ipost.state := by
  obtain ⟨post, hrun, hstack, hcode, live⟩ :=
    Creation.pair_create2_initialize_live hfork hstatic hinit hnonce hdepth hfresh hgas hroom
  refine ⟨post, hrun, hstack, ?_⟩
  intro isevm ib iG htarget hstor hcodeAt caller value nonstatic codeEq fork selector size guard
    representable freshOutput sentry0 sentry1 token1 token0 wethImage wethFoot wethStor sumNof
  obtain ⟨ipost, ⟨run⟩, initialized⟩ := live htarget hstor caller value nonstatic codeEq fork
    selector size guard representable freshOutput sentry0 sentry1
  refine ⟨ipost, ⟨run⟩, ?_⟩
  obtain ⟨codes, bals, stors⟩ := initialize_run_frame codeEq fork selector run
  have wethNe : isevm.currentTarget ≠ weth := by
    rw [htarget]
    exact fun h => wethApart h.symm
  have wethStor' : ipost.state.getStor weth = b.state.getStor weth :=
    (stors weth wethNe).trans wethStor
  have balEq : ipost.state.bal = ib.state.bal := funext bals
  rw [← htarget] at initialized tracked noAllowance pairNonzero notSystem
  rw [token1] at initialized
  exact
    { pairCode := by
        change some (ipost.getCode isevm.currentTarget).toList = some UniswapV2Pair.code.toList
        rw [codes]
        change some (ib.state.getCode isevm.currentTarget).toList = _
        rw [hcodeAt, htarget]
        change some (post.getCode _).toList = _
        rw [hcode]
      pairRep := initialized
      token := rfl
      unlocked := rfl
      wethCode := by
        change some (ipost.getCode weth).toList = _
        rw [codes]
        exact wethImage
      wethFoot := by
        rw [balEq]
        change FootInv K₀ (Devm.getStor ipost weth) _
        rw [stors weth wethNe]
        exact wethFoot
      sumNof := by
        rw [balEq]
        exact sumNof
      tracked := tracked
      noAllowance := fun g row => by
        rw [wethStor']
        exact noAllowance g row
      reserve := Nat.zero_le _
      apart := wethNe
      distinct := token0
      notSystem := notSystem
      pairNonzero := pairNonzero
      wethNotPrecompile := wethNotPrecompile }

end Blanc.Composition.UniswapV2PairWeth9Joint
