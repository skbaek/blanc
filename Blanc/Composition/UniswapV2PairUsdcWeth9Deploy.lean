import Blanc.Composition.UniswapV2PairUsdcWeth9Checkpoint
import Blanc.Composition.UniswapV2PairWeth9Deploy

/-!
# C7: the two-token joint checkpoint by deployment

`pair_usdc_weth9_create2_jointCheckpoint2` restates the predecessor's
`pair_weth9_create2_jointCheckpoint` with USDC as `token0`: the Pair's `CREATE2` deployment and
every successful `initialize` naming USDC and WETH9, at a world carrying both tokens' checkpoint
facts, give a world satisfying `JointCheckpoint2` with the initialized model state and no tracked
Pair row.

The WETH9 side and the Pair's storage are the predecessor's theorem.  USDC's side is a frame fact:
the `initialize` frame touches only the Pair's storage (`initialize_run_frame`), and `usdcApart`
puts USDC's account outside it, so USDC's three codes, its implementation slot, its footprint and
the new address's rows are those of the `initialize` world, which agrees with the deployment world
on USDC's storage.  The never-signer premise does not appear: it belongs to the headlines that need
the holder laws (decision `usdc-neversigner-premise-form`).
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.Weth9
  Blanc.Composition.UniswapV2PairWeth9Joint

/-- **C7: the two-token joint checkpoint by deployment.**  As `pair_weth9_create2_jointCheckpoint`,
with `initialize` naming USDC as `token0` and WETH9 as `token1`, and USDC's checkpoint facts at the
`initialize` world (installed codes, footprint invariant, storage agreeing with the deployment
world's, the new address's balance row tracked, unflagged, with no tracked allowance row, USDC no
precompile). -/
theorem pair_usdc_weth9_create2_jointCheckpoint2 {usdc weth : Adr} {KU : Usdc.Key → Prop}
    {KW : Weth9.Key → Prop}
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
    (usdcApart : usdc ≠ create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList)
    (pairNonzero : create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList ≠ 0)
    (notSystem :
      create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList ≠ systemAddress)
    (wethTracked : KW (.bal (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList)))
    (wethNoAllowance : ∀ g, KW (.allow (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList) g) →
      (b.state.getStor weth).get
        (Weth9.allowSlot (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList) g) = 0)
    (wethNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp weth)
    (usdcTracked : KU (.bal (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList)))
    (usdcNoAllowance : ∀ g, KU (.allow (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList) g) →
      (b.state.getStor usdc).get
        (Usdc.allowSlot (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList) g) = 0)
    (usdcNotFrozen : Usdc.frozenBit ((b.state.getStor usdc).get
        (Usdc.balSlot (create2NewAddress sevm.currentTarget salt UniswapV2Pair.Creation.code.toList))) = false)
    (usdcNotPrecompile : ∀ s : BenvStat, CoveredFork s.fork → ¬ s.rules.isPrecomp usdc) :
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
        initializeToken0 isevm = usdc →
        usdc ≠ weth →
        some (ib.state.getCode weth).toList = weth9Sem.image →
        Weth9.FootInv KW (ib.state.getStor weth) (ib.state.bal weth) →
        ib.state.getStor weth = b.state.getStor weth →
        SumNof ib.state.bal →
        Usdc.UsdcInstalled usdc ib.state →
        Usdc.FootInv KU (ib.state.getStor usdc) →
        ib.state.getStor usdc = b.state.getStor usdc →
        ∃ ipost, Nonempty (Exec 0 isevm
            (St ib [] Mem.empty (iG + initializeStorageCharge isevm ib + 377)) (.ok ipost)) ∧
          JointCheckpoint2 isevm.currentTarget usdc weth KU KW (fun _ => False)
            (initializedState sevm.currentTarget
              (UniswapV2Pair.Creation.domainSeparator sevm.benvStat.chainId.toB256 isevm.currentTarget)
              usdc weth) ipost.state := by
  obtain ⟨post, hrun, hstack, h⟩ := pair_weth9_create2_jointCheckpoint hfork hstatic hinit hnonce
    hdepth hfresh hgas hroom wethApart pairNonzero notSystem wethTracked wethNoAllowance
    wethNotPrecompile
  refine ⟨post, hrun, hstack, ?_⟩
  intro isevm ib iG htarget hstor hcodeAt caller value nonstatic codeEq fork selector size guard
    representable freshOutput sentry0 sentry1 token1 token0 distinct wethImage wethFoot wethStor
    sumNof usdcInstalled usdcFoot usdcStor
  obtain ⟨ipost, ⟨run⟩, joint⟩ := h htarget hstor hcodeAt caller value nonstatic codeEq fork
    selector size guard representable freshOutput sentry0 sentry1 token1
    (by rw [token0]; exact distinct) wethImage wethFoot wethStor sumNof
  rw [token0] at joint
  refine ⟨ipost, ⟨run⟩, ?_⟩
  obtain ⟨codes, -, stors⟩ := initialize_run_frame codeEq fork selector run
  have usdcNe : isevm.currentTarget ≠ usdc := by
    rw [htarget]
    exact fun h => usdcApart h.symm
  have ipostStor : ipost.state.getStor usdc = ib.state.getStor usdc := stors usdc usdcNe
  have usdcStor' : ipost.state.getStor usdc = b.state.getStor usdc := ipostStor.trans usdcStor
  rw [← htarget] at usdcTracked usdcNoAllowance usdcNotFrozen
  exact
    { weth9 := joint
      usdcInstalled :=
        { proxy := by
            change some (ipost.getCode usdc).toList = _
            rw [codes]
            exact usdcInstalled.proxy
          impl := by
            change some (ipost.getCode Usdc.usdcImpl).toList = _
            rw [codes]
            exact usdcInstalled.impl
          lib := by
            change some (ipost.getCode Usdc.usdcLib).toList = _
            rw [codes]
            exact usdcInstalled.lib
          slot := by
            rw [ipostStor]
            exact usdcInstalled.slot
          implApart := usdcInstalled.implApart
          libApart := usdcInstalled.libApart }
      usdcFoot := by
        rw [ipostStor]
        exact usdcFoot
      token0 := rfl
      tracked := usdcTracked
      notFrozen := by
        rw [usdcStor']
        exact usdcNotFrozen
      noAllowance := fun g row => by
        rw [usdcStor']
        exact usdcNoAllowance g row
      reserve := Nat.zero_le _
      apart := usdcNe
      usdcNotPrecompile := usdcNotPrecompile }

end Blanc.Composition.UniswapV2PairUsdcWeth9
