import Blanc.Lift.UniswapV2Pair.Creation.Walk
import Blanc.Lift.UniswapV2Pair.Creation.Check
import Blanc.Lift.UniswapV2Pair.Creation.Jumps

/-!
# Deploying the Uniswap V2 Pair by `CREATE2`

* `pair_create`: the recorded creation code (11,636 bytes, `Creation/Cert.lean`), executed as a
  zero-value creation message with at least 2,400,000 gas under a covered fork, succeeds,
  installs exactly the certified runtime `Blanc.Lift.UniswapV2Pair.code` at the new address, and
  leaves exactly the constructor's storage: `unlocked = 1` (slot 12), the EIP-712 domain separator
  over the frame's chain id and the new address (slot 3) and the creator (slot 5).
* `pair_create2`: a `CREATE2` from any non-static frame (the factory) whose memory window holds
  that creation code is a compiled step that pushes `create2NewAddress creator salt code`, and the
  world after it has the certified runtime and the constructor storage there, with the factory
  (the creating frame) as `factory` and the domain separator over the creating frame's chain id
  and that address.

No hash premise: the address is the actual `create2NewAddress` of the memory slice, the domain
separator is the digest the walk computes (`Walk.lean`).
-/

namespace Blanc.Lift.UniswapV2Pair.Creation

open Jaune Blanc.Lift

/-- The constructor costs at most 80,000 gas. -/
theorem ctorCost_le (sevm : Sevm) (b : Devm) : ctorCost sevm b ≤ 80000 := by
  have hl : ∀ (b : Devm) (k : B256), sloadCost sevm b k ≤ 2100 := by
    intro b k; unfold sloadCost; split <;> decide
  have hs : ∀ (b : Devm) (k v : B256), sstoreCost sevm b k v ≤ 22100 := by
    intro b k v; unfold sstoreCost sstoreValueCost; split_ifs <;> decide
  have := hl (w2 sevm b) 5
  have := hs b 12 1
  have := hs (w1 sevm b) 3 (domainSeparator sevm.benvStat.chainId.toB256 sevm.currentTarget)
  have := hs (w3 sevm b) 5 sevm.caller.toB256
  unfold ctorCost
  omega

/-- **Deploying the Pair.**  The creation code, executed as a zero-value creation message with
enough gas under a covered fork, succeeds without error; the new account's code is the certified
runtime and its storage is exactly the constructor's. -/
theorem pair_create (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hgas : 2400000 ≤ msg.gas) (hfork : CoveredFork msg.benv.stat.fork)
    (hstatic : msg.isStatic = false)
    (hmax : 11293 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.UniswapV2Pair.code.toList ∧
      Devm.getStor post msg.currentTarget =
        ctorStor msg.benv.stat.chainId.toB256 msg.currentTarget msg.caller Stor.empty ∧
      post.error = .none := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  have hstat : (initSevm (createSeed msg benv)).benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have hempty : Devm.getStor (initDevm (createSeed msg benv))
      (initSevm (createSeed msg benv)).currentTarget = Stor.empty := by
    show benv.state.getStor msg.currentTarget = _
    rw [benvAfterTransfer_ok_getStor htransfer, processCreateMessage_msg_getStor_currentTarget]
  have hstor : ∀ x, (Devm.getStor (initDevm (createSeed msg benv))
      (initSevm (createSeed msg benv)).currentTarget).get x = 0 := fun x => by
    rw [hempty]
    rfl
  have hle := ctorCost_le (initSevm (createSeed msg benv)) (initDevm (createSeed msg benv))
  obtain ⟨raw, hrun, hout, herr, hst, hgasLeft⟩ :=
    ctor_run (sevm := initSevm (createSeed msg benv)) (by rw [hstat]; exact hfork) hstatic hcode
      hvalue hstor (msg.gas - ctorCost (initSevm (createSeed msg benv))
        (initDevm (createSeed msg benv)))
  have hpre : St (initDevm (createSeed msg benv)) [] Mem.empty
      (msg.gas - ctorCost (initSevm (createSeed msg benv)) (initDevm (createSeed msg benv)) +
        ctorCost (initSevm (createSeed msg benv)) (initDevm (createSeed msg benv))) =
      initDevm (createSeed msg benv) :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre] at hrun
  have hwin : raw.output = Blanc.Lift.UniswapV2Pair.code.toList := by
    rw [hout, runtimeWindow_eq]
  have hlen : raw.output.length = 11293 := by rw [hout, runtimeWindow_length]
  obtain ⟨post, hpost, hcodePost, hstorPost, herrPost⟩ := liftCreate_ok cert_check jumps_ok msg
    hcodeAddress hcode hfork htransfer hrun (by rw [herr]; rfl)
    (by rw [hwin]; exact runtime_head)
    (by rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega) (by rw [hlen]; exact hmax)
  refine ⟨post, hpost, hcodePost.trans hwin, ?_, herrPost⟩
  rw [hstorPost]
  show Devm.getStor raw (initSevm (createSeed msg benv)).currentTarget = _
  rw [hst, hempty, hstat]
  rfl

/-- Every covered fork admits the Pair's runtime and creation code sizes. -/
theorem covered_codeLimits {s : BenvStat} (h : CoveredFork s.fork) :
    11293 ≤ s.rules.code.maxCodeSize ∧ 11636 ≤ s.rules.code.maxInitCodeSize := by
  unfold BenvStat.rules
  exact h.cases (motive := fun f => 11293 ≤ (Fork.ruleSet f).code.maxCodeSize ∧
    11636 ≤ (Fork.ruleSet f).code.maxInitCodeSize) (by decide) (by decide) (by decide)
    (by decide)

/-- **Deploying the Pair by `CREATE2`.**  In a non-static frame under a covered fork (the factory),
a zero-endowment `CREATE2` whose memory window holds the Pair creation code, with the creator's
nonce below the maximum, positive depth, an empty target and at least 2,400,000 gas forwarded,
is a compiled step.  It pushes the address `create2NewAddress creator salt code`, and the world
after it holds the certified runtime there with the constructor storage: `unlocked = 1`, the
domain separator over the creating frame's chain id and that address, and the creator as
`factory`. -/
theorem pair_create2 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
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
      Devm.getStor post (create2NewAddress sevm.currentTarget salt code.toList) =
        ctorStor sevm.benvStat.chainId.toB256
          (create2NewAddress sevm.currentTarget salt code.toList) sevm.currentTarget
          Stor.empty := by
  have hlimits := covered_codeLimits hfork
  have hsz : sz.toNat = 11636 := by
    have hlen := congrArg List.length hinit
    rw [create2InitCode, Array.sliceD_eq_map, List.length_map, List.length_range,
      code_toList_length] at hlen
    exact hlen
  rw [← hinit] at hfresh ⊢
  obtain ⟨child, hchild, hcode, hstor, herr⟩ := pair_create (createMsg sevm
      (create2Prepared sevm b S M G i sz
        (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz)))
      (except64th G) 0 (create2NewAddress sevm.currentTarget salt (create2InitCode M i sz))
      (create2InitCode M i sz)) rfl rfl
    (by
      show ByteArray.mk ⟨create2InitCode M i sz⟩ = code
      rw [hinit, ByteArray.toList_eq_toList_data])
    hgas hfork rfl hlimits.1
  refine ⟨_, create2_runCompiled hfork (by rw [hsz]; exact hlimits.2) hstatic
    (not_lt_of_ge (B256.zero_le _)) hnonce hdepth hfresh hchild herr hroom, rfl, hcode, hstor⟩

end Blanc.Lift.UniswapV2Pair.Creation
