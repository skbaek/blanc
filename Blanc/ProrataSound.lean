-- ProrataSound.lean : open-contract preservation for PRORATA.

import Blanc.ProrataPreservation
import Blanc.ProrataRead

namespace Blanc

open Jaune

namespace Prorata

private lemma BodyEntry.with_pre
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {body : Func} {ca : Adr}
    (h : BodyEntry fs sevm pre post body)
    (hpre : prorataSpec.Pre ca sevm pre) :
    ∃ entry, prorataSpec.Pre ca sevm entry ∧
      Func.Run fs sevm entry body post := by
  rcases h with ⟨entry, hstor, hbal, hcode, hrun⟩
  refine ⟨entry, ?_, hrun⟩
  exact ContractSpec.Pre.of_eqs hpre (congrFun hcode ca) hbal
    (congrFun hstor ca)

private theorem deposit_post
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {ca : Adr}
    (hca : sevm.currentTarget = ca)
    (hpre : prorataSpec.Pre ca sevm pre)
  (hrun : Func.Run fs sevm pre deposit post) :
    prorataSpec.Post ca sevm post := by
  have he := deposit_effect hrun
  have h_inv_pre : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (Devm.getBal pre sevm.currentTarget) := by
    rw [hca]
    exact hpre.inv.left hca
  have hinv := DepositEffect.preserves_inv he h_inv_pre
  rcases he with ⟨_, _, _, _, hbal, _, _, _⟩
  refine ⟨?_, ?_⟩
  · rw [hbal]
    exact hpre.side
  · change Inv (Devm.getStor post ca) 0 (Devm.getBal post ca)
    simpa only [hca] using hinv

private theorem convertToShares_post
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {ca : Adr}
    (hpre : prorataSpec.Pre ca sevm pre)
    (hrun : Func.Run fs sevm pre convertToShares post) :
    prorataSpec.Post ca sevm post := by
  have he := convertToShares_effect hrun
  rcases he with ⟨_, _, _, _, hstor, hbal, hcode, _⟩
  exact prorataSpec.post_of_pre
    (ContractSpec.Pre.of_eqs hpre (congrFun hcode ca) hbal
      (congrFun hstor ca))

private theorem convertToAssets_post
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {ca : Adr}
    (hpre : prorataSpec.Pre ca sevm pre)
    (hrun : Func.Run fs sevm pre convertToAssets post) :
    prorataSpec.Post ca sevm post := by
  have he := convertToAssets_effect hrun
  rcases he with ⟨_, _, _, hstor, hbal, hcode, _⟩
  exact prorataSpec.post_of_pre
    (ContractSpec.Pre.of_eqs hpre (congrFun hcode ca) hbal
      (congrFun hstor ca))

private theorem donate_post
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {ca : Adr}
    (hpre : prorataSpec.Pre ca sevm pre)
    (hrun : Func.Run fs sevm pre donate post) :
    prorataSpec.Post ca sevm post := by
  have hstor : Devm.getStor post = Devm.getStor pre :=
    (Func.of_inv Devm.getStor Devm.getStor (by func_inv) hrun).symm
  have hbal : Devm.getBal post = Devm.getBal pre :=
    (Func.of_inv Devm.getBal Devm.getBal (by func_inv) hrun).symm
  have hcode : Devm.getCode post = Devm.getCode pre :=
    (Func.of_inv Devm.getCode Devm.getCode (by func_inv) hrun).symm
  exact prorataSpec.post_of_pre
    (ContractSpec.Pre.of_eqs hpre (congrFun hcode ca) hbal
      (congrFun hstor ca))

private theorem withdraw_post
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {ca : Adr}
    (hca : sevm.currentTarget = ca)
    (hpre : prorataSpec.Pre ca sevm pre)
    (ih : Exec.InvDepth sevm.depth ca prorataSpec.prog
      (prorataSpec.PreWf ca) (prorataSpec.Post ca))
    (hrun : Func.Run fs sevm pre withdraw post) :
    prorataSpec.Post ca sevm post := by
  let p := Sevm.argWord sevm 0 *
    (Devm.getBal pre sevm.currentTarget + 1) /
      ((Devm.getStor pre sevm.currentTarget).get supplySlot + offset)
  have hpays := withdraw_pays_exactly hrun
  change ∃ callPre callPost guardPost returnPre,
    WithdrawPreCallEffect sevm pre callPre ∧
    AcceptedPayout sevm p callPre callPost guardPost returnPre ∧
    Devm.getStor post = Devm.getStor callPost ∧
    Devm.getBal post = Devm.getBal callPost ∧
    ReturnsWord p post at hpays
  rcases hpays with
    ⟨callPre, callPost, guardPost, returnPre, hpreCall, hpayout,
      hstorPost, hbalPost, _⟩
  have hinvPre : Inv (Devm.getStor pre sevm.currentTarget) sevm.value
      (pre.getBal sevm.currentTarget) := by
    rw [hca]
    exact hpre.inv.left hca
  have hinvCallRaw : Inv (Devm.getStor callPre sevm.currentTarget) 0
      (pre.getBal sevm.currentTarget - p) := by
    simpa only [p] using
      WithdrawPreCallEffect.settlement_inv hpreCall hinvPre
  have heffect := hpreCall
  unfold WithdrawPreCallEffect at heffect
  dsimp at heffect
  rcases heffect with
    ⟨_, _, _, hbalCall, hcodeCall, _, _, _, _⟩
  have hcode :
      some (callPre.getCode ca).toList = Prog.compile prorataSpec.prog := by
    rw [hcodeCall]
    exact hpre.code
  have hside : prorataSpec.Side callPre.getBal := by
    rw [hbalCall]
    exact hpre.side
  have hinv : Inv (Devm.getStor callPre ca) 0
      (callPre.getBal ca - p) := by
    simpa only [p, hca, hbalCall] using hinvCallRaw
  rcases hpayout with
    ⟨gasWord, xs, parent, child, xl, delegated, nextAddress, code, avail, pc,
      _, _, _, _, _, hdepth, _, hparentState, _, _, _, hdelegation,
      hfilled, hpm, hclean, _, hcallPostState, _, _, _⟩
  let childMsg :=
    callMsg sevm parent
      (min gasWord.toNat (except64th avail) +
        (if p.toNat = 0 then 0 else gCallStipend))
      p sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
      ((callPre.memory.read 0 0).1) code delegated
  change ProcessMessage childMsg xl (.ok child) at hpm
  have hcState : childMsg.benv.state = callPre.state := by
    change parent.state = callPre.state
    exact hparentState
  have hcStv : childMsg.shouldTransferValue = true := rfl
  have hcCaller : childMsg.caller = ca := by
    change sevm.currentTarget = ca
    exact hca
  have hcValue : childMsg.value = p := rfl
  have hcTarget : childMsg.currentTarget = sevm.caller.toB256.toAdr := rfl
  have hcCodeAddress : childMsg.codeAddress = some nextAddress := rfl
  obtain ⟨r0, hbody, hset⟩ := ProcessMessage.iff_body.mp hpm
  unfold FrameBody at hbody
  rcases hbt : childMsg.benvAfterTransfer with e | benv <;>
    rw [hbt] at hbody
  · rw [hbody.2, processMessage.settle_error] at hset
    cases hset
  have hexec : ExecuteCode (childMsg.withBenv benv) xl r0 := hbody
  rcases of_benvAfterTransfer hcStv hbt with
    ⟨stMid, hsub, hbenv⟩
  rw [hcState, hcCaller, hcValue] at hsub
  have hbenvState : benv.state = stMid.addBal sevm.caller.toB256.toAdr p := by
    rw [hbenv, hcTarget, hcValue]
    rfl
  have hchildPre : prorataSpec.Pre ca
      (initSevm (childMsg.withBenv benv))
      (initDevm (childMsg.withBenv benv)) := by
    apply ContractSpec.Pre.child_of_outbound_transfer
      (st := callPre.state) (st_mid := stMid)
      (target := sevm.caller.toB256.toAdr) (value := p)
    · exact hcode
    · exact hside
    · exact hinv
    · exact hsub
    · exact hbenvState
    · exact hcTarget
    · exact hcValue
  obtain ⟨evm2, hr0, hsettle⟩ := processMessage.settle_ok_cases hset.symm
  subst hr0
  rcases hsettle with ⟨herr, heq⟩ | ⟨herr, hchild⟩
  · have : child.error.isSome = true := by
      rw [← heq]
      exact herr
    simp [hclean] at this
  rw [hchild] at hexec herr
  have hchildPost : prorataSpec.Post ca
      (initSevm (childMsg.withBenv benv)) child := by
    have hcCodeAddress' :
        (childMsg.withBenv benv).codeAddress = some nextAddress :=
      hcCodeAddress
    rcases of_executeCode_someCode hcCodeAddress' hexec with
      ⟨_, _, hhandle⟩ | ⟨_, exn, hxl, hhandle⟩
    · have hchildState :
          child.state = (initDevm (childMsg.withBenv benv)).state := by
        exact state_of_executePrecomp_ok hhandle herr
      exact prorataSpec.post_of_pre (hchildPre.state_eq hchildState)
    · have hexn : exn = .ok child :=
        exec_ok_of_handleError hhandle herr
      rw [hxl, hexn] at hfilled
      obtain ⟨hchildExec⟩ := hfilled
      have hat : Prog.At prorataSpec.prog ca 0
          (initSevm (childMsg.withBenv benv))
          (initDevm (childMsg.withBenv benv)) := by
        refine ⟨hchildPre.code, ?_⟩
        intro hchildTarget
        refine ⟨?_, rfl⟩
        have htargetCa : sevm.caller.toB256.toAdr = ca :=
          hcTarget.symm.trans hchildTarget
        change some code.toList = Prog.compile prorataSpec.prog
        rcases hdelegation with
          ⟨_, _, hcodeSelf, _⟩ |
          ⟨d, hsome, _, _, _⟩
        · rw [hcodeSelf, htargetCa]
          exact hcode
        · exfalso
          have hnot : ¬ isValidDelegation (callPre.getCode ca) :=
            not_delegation_of_compile hcode
          apply hnot
          unfold getDelegatedCodeAddress at hsome
          split at hsome
          · rename_i hvalid
            rw [htargetCa] at hvalid
            exact hvalid
          · cases hsome
      have hdepthLt :
          (initSevm (childMsg.withBenv benv)).depth < sevm.depth := by
        change sevm.depth - 1 < sevm.depth
        omega
      exact ih 0
        (initSevm (childMsg.withBenv benv))
        (initDevm (childMsg.withBenv benv))
        (.ok child) hchildExec hdepthLt hat
        ⟨hchildPre, fun _ => Mem.wf_empty⟩
  have hcallPost : prorataSpec.Post ca sevm callPost :=
    ContractSpec.Post.of_state_eq hchildPost hcallPostState
  refine ⟨?_, ?_⟩
  · rw [hbalPost]
    exact hcallPost.side
  · show Inv (Devm.getStor post ca) 0 (post.getBal ca)
    rw [congrFun hstorPost ca, congrFun hbalPost ca]
    exact hcallPost.inv

/-- Every successful execution of the hand-shaped PRORATA program preserves
the open-contract invariant, without an entry-memory premise. -/
theorem prorataSpec_soundNoMem (ca : Adr) :
    prorataSpec.SoundNoMem ca := by
  intro sevm pre post hrun hca ih hpre
  have ihDepth : Exec.InvDepth sevm.depth ca prorataSpec.prog
      (prorataSpec.PreWf ca) (prorataSpec.Post ca) := by
    intro pc' sevm' devm' exn'
    cases exn'
    · simp only [ifOk, implies_true]
    · apply ih
  dsimp only [Prog.Run] at hrun
  cases hrun
  rename (_ = _) => hentry
  rename (Func.Run _ _ _ _ _) => hmain
  rename (Devm.Burn _ _) => hburn
  rename Devm => entry
  cases hentry
  have hpreEntry : prorataSpec.Pre ca sevm entry :=
    hpre.state_eq hburn.state.symm
  change Func.Run _ sevm entry prorataMain post at hmain
  rcases classify_prorataMain_success hmain with
    hdeposit | hwithdraw | hshares | hassets | hdonate
  · rcases BodyEntry.with_pre hdeposit hpreEntry with
      ⟨bodyPre, hbodyPre, hbodyRun⟩
    exact deposit_post hca hbodyPre hbodyRun
  · rcases BodyEntry.with_pre hwithdraw hpreEntry with
      ⟨bodyPre, hbodyPre, hbodyRun⟩
    exact withdraw_post hca hbodyPre ihDepth hbodyRun
  · rcases BodyEntry.with_pre hshares hpreEntry with
      ⟨bodyPre, hbodyPre, hbodyRun⟩
    exact convertToShares_post hbodyPre hbodyRun
  · rcases BodyEntry.with_pre hassets hpreEntry with
      ⟨bodyPre, hbodyPre, hbodyRun⟩
    exact convertToAssets_post hbodyPre hbodyRun
  · rcases BodyEntry.with_pre hdonate hpreEntry with
      ⟨bodyPre, hbodyPre, hbodyRun⟩
    exact donate_post hbodyPre hbodyRun

/-- The memory-carrying soundness form for downstream generic consumers. -/
theorem prorataSpec_sound (ca : Adr) : prorataSpec.Sound ca :=
  ContractSpec.SoundNoMem.sound (prorataSpec_soundNoMem ca)

/-- Every successful PRORATA subexecution preserves the invariant without an
entry-memory premise. -/
theorem prorataSpec_preservesNoMem (ca : Adr) :
    prorataSpec.PreservesNoMem ca :=
  prorataSpec.preserves_noMem ca (prorataSpec_soundNoMem ca)

/-- The memory-carrying preservation form consumed by the message and block
execution ladders. -/
theorem prorataSpec_preserves (ca : Adr) : prorataSpec.Preserves ca :=
  ContractSpec.PreservesNoMem.preserves (prorataSpec_preservesNoMem ca)

end Prorata

end Blanc
