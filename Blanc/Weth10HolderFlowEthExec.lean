import Blanc.Weth10HolderFlowFlashChronology
import Blanc.Weth10HolderFlowExecAccounting
import Blanc.Weth10HolderFlowSelectorFacts

/-!
Proof-indexed recursive ETH accounting for installed WETH10 execution.

This module is downstream of the compiled classifier.  It keeps the concrete
`Exec` witness in the induction predicate so retained action lists cannot be
detached from the child slots that produced them.  Generic foreign execution
is handled at the interpreter boundary; the remaining at-target handler is
phrased over the compiled WETH10 program.
-/

namespace Blanc

open Jaune

namespace Weth10

/-- ETH-side local spelling of ABI address normalization. -/
private theorem normalizedAddressArg_eq_toAdr_toB256_eth
    (e : Sevm) (k : B256) :
    normalizedAddressArg e k = (Sevm.argWord e k).toAdr.toB256 := by
  have lowMask (x : UInt64) :
      (0x00000000ffffffff : UInt64) &&& x =
        x.toUInt32.toUInt64 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_and, UInt64.toNat_toUInt32,
      UInt32.toNat_toUInt64]
    rw [Nat.and_comm]
    change x.toNat &&& 2 ^ 32 - 1 = x.toNat % 2 ^ 32
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  have andMax (x : UInt64) : UInt64.max &&& x = x := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_and]
    have hmax : UInt64.max.toBitVec = BitVec.allOnes 64 := by rfl
    rw [hmax]
    exact BitVec.allOnes_and
  have b128AndMax (x : B128) : B128.max &&& x = x := by
    apply Prod.ext <;> apply andMax
  have hmask : (~~~ addressMask) =
      (⟨⟨0, 0x00000000ffffffff⟩, B128.max⟩ : B256) := by
    decide +kernel
  unfold normalizedAddressArg
  rw [hmask]
  rcases Sevm.argWord e k with ⟨⟨high, middle⟩, low⟩
  simp only [B256.toAdr, Adr.toB256, B256.and_eq_and_prod_and,
    B128.and_eq_and_prod_and, UInt64.zero_and]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact lowMask middle
  · exact b128AndMax low

/-- A filled recursive slot preserves every already-installed nonempty code
cell. -/
private theorem Xlot.codeRel_of_filled_eth {xl : Xlot}
    (filled : xl.Filled) : Xlot.Rel Devm.CodePreserve xl := by
  rcases xl with _ | ⟨⟨pc, sevm, pre⟩, out⟩
  · trivial
  · rcases filled with ⟨run⟩
    change Execution.Rel Devm.CodePreserve pre out
    cases out with
    | error err => exact fun a ha => Exec.preserves_getCode run a ha
    | ok post => exact fun a ha => Exec.preserves_getCode run a ha

/-- The accepted value child cannot increase the global world-balance sum. -/
private theorem AcceptedValueCallTrace.guard_sum_le
    {e : Sevm} {target value : B256} {callPre guardPost : Devm}
    (trace : AcceptedValueCallTrace e target value callPre guardPost) :
    sum guardPost.state.bal ≤ sum callPre.state.bal := by
  have hnoninc := ProcessMessage.balance_effect
    (Xlot.balance_rel_of_filled trace.retained.retained.toFilled)
    trace.retained.run
  change sum trace.child.state.bal ≤
    sum trace.childMessage.benv.state.bal at hnoninc
  rw [trace.childMessage_eq] at hnoninc
  simp only [callMsg] at hnoninc
  rw [trace.parent_state] at hnoninc
  rw [← trace.guard_state] at hnoninc
  exact hnoninc

/-- The same accepted child preserves the installed WETH10 code cell, so a
later callback in the same selector can use the recursive code premise. -/
private theorem AcceptedValueCallTrace.guard_code_eq
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {target value : B256} {callPre guardPost : Devm}
    (trace : AcceptedValueCallTrace e target value callPre guardPost)
    (installed : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp)) :
    guardPost.getCode ca = callPre.getCode ca := by
  have hinv : trace.retained.slot.InvGetCode :=
    Xlot.invGetCode_of_rel
      (Xlot.codeRel_of_filled_eth trace.retained.retained.toFilled)
  have hne :
      (trace.childMessage.benv.state.getCode ca).toList ≠ [] := by
    rw [trace.childMessage_eq]
    simp only [callMsg]
    rw [trace.parent_state]
    exact fun hempty => Prog.compile_ne_nil
      (installed.symm.trans (congrArg some hempty))
  have hcode := ProcessMessage.preserves_getCode_gen hinv
    trace.retained.run ca hne
  change trace.child.getCode ca =
    trace.childMessage.benv.state.getCode ca at hcode
  rw [trace.childMessage_eq] at hcode
  simp only [callMsg] at hcode
  rw [trace.parent_state] at hcode
  have hguard := congrArg (fun state : State => state.getCode ca)
    trace.guard_state
  exact hguard.trans hcode

/-- Proof-indexed body predicate consumed by `lift_core`.  A direct/root
premise is required only when the frame actually executes at `ca`; foreign
continuations satisfy it vacuously.  The installed-program premise rules out
synthetic CREATE frames at the live contract address, and the global-sum
premise makes every otherwise-unclassified inward credit non-wrapping. -/
def Exec.CoreEthSound (dp : DeployParams) (ca : Adr)
    (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (run : Exec pc sevm pre out)
    (hcommit : Execution.commits out = true),
    Prog.At (weth10 dp) ca pc sevm pre →
    (sevm.currentTarget = ca →
      Exec.Frame.IsRoot (Exec.Frame.ofRun run hcommit) ∧
      sevm.codeAddress = some ca) →
    sum pre.state.bal < 2 ^ 256 →
    EthBound ca pre.state
      (Execution.committedPost out hcommit).state
      (Exec.bodyEthActions dp ca run hcommit)

/-- CREATE's nonce/access-list preparation leaves the world balance map
unchanged. -/
theorem genericCreate_prepared_bal
    (sevm : Sevm) (pre : Devm) (newAddress : Adr) :
    (addAccessedAddress
      (((pre.withGasLeft
          (pre.gasLeft - except64th pre.gasLeft)).withReturnData
        []).incrNonce sevm.currentTarget) newAddress).state.bal =
      pre.state.bal := by
  have haccess := addAccessedAddress_instructionFrame
    (((pre.withGasLeft
        (pre.gasLeft - except64th pre.gasLeft)).withReturnData
      []).incrNonce sevm.currentTarget) newAddress
  calc
    _ = (((pre.withGasLeft
          (pre.gasLeft - except64th pre.gasLeft)).withReturnData
        []).incrNonce sevm.currentTarget).state.bal :=
      congrArg State.bal haccess.state.symm
    _ = pre.state.bal := State.incrNonce_bal

/-- A zero-value message entry preserves the complete balance map, including
the self-call case where caller and callee coincide. -/
theorem Msg.benvAfterTransfer_bal_eq_of_value_eq_zero
    {msg : Msg} {post : Benv}
    (hzero : msg.value = 0)
    (hrun : msg.benvAfterTransfer = .ok post) :
    post.state.bal = msg.benv.state.bal := by
  cases hstv : msg.shouldTransferValue with
  | false =>
      have hnot : ¬ msg.shouldTransferValue = true := by
        simp [hstv]
      have h := of_benvAfterTransfer_no hnot hrun
      subst post
      rfl
  | true =>
      rcases of_benvAfterTransfer hstv hrun with
        ⟨debit, hsub, rfl⟩
      rw [hzero] at hsub ⊢
      change (debit.addBal msg.currentTarget 0).bal =
        msg.benv.state.bal
      have hdebitBal : debit.bal = msg.benv.state.bal := by
        rcases State.of_subBal hsub with ⟨_, rfl⟩
        funext address
        unfold State.bal
        by_cases hcaller : msg.caller = address
        · subst address
          rw [State.setBal_get_self]
          exact B256.sub_zero_exact _
        · rw [State.setBal_get_ne hcaller]
      have haddBal :
          (debit.addBal msg.currentTarget 0).bal = debit.bal := by
        funext address
        unfold State.addBal State.bal
        by_cases htarget : msg.currentTarget = address
        · subst address
          rw [State.setBal_get_self]
          exact B256.add_zero_exact _
        · rw [State.setBal_get_ne htarget]
      exact haddBal.trans hdebitBal

/-- Message entry at value zero funds every possible root ordinary-mint
label (whose ETH weight is necessarily zero) without requiring the external
caller inequality used by transaction entry.  This is the internal callback
counterpart of `Exec.entryEthBound`. -/
theorem Exec.entryEthBound_of_value_eq_zero
    {dp : DeployParams} {ca : Adr} {msg : Msg} {benv : Benv}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hinit : (⟨pc, sevm, pre⟩ : Evm) =
      initEvm (msg.withBenv benv))
    (hcommit : Execution.commits out = true)
    (hzero : msg.value = 0) :
    EthBound ca msg.benv.state pre.state
      (Exec.entryEthActions dp ca run hcommit) := by
  have hpc := congrArg Evm.pc hinit
  have hsevm := congrArg Evm.sta hinit
  have hpre := congrArg Evm.dyna hinit
  dsimp only [initEvm] at hpc hsevm hpre
  subst pc
  subst sevm
  subst pre
  let root : Exec.Frame := Exec.Frame.ofRun run hcommit
  have hmint :
      flowActionsEthMint
          (Exec.entryEthActions dp ca run hcommit) ≤ msg.value.toNat := by
    have h := root.flowActionsEthMint_entryEthActions_le_value
      (dp := dp) (ca := ca)
    simpa [root, Exec.entryEthActions, Exec.Frame.ofRun,
      initSevm, Msg.withBenv] using h
  have hmintZero :
      flowActionsEthMint
          (Exec.entryEthActions dp ca run hcommit) = 0 := by
    rw [hzero] at hmint
    exact Nat.eq_zero_of_le_zero hmint
  have hredeem :
      flowActionsEthRedemption
          (Exec.entryEthActions dp ca run hcommit) = 0 :=
    flowActionsEthRedemption_entryEthActions_eq_zero _
  have hbal := Msg.benvAfterTransfer_bal_eq_of_value_eq_zero
    hzero htransfer
  unfold EthBound
  rw [hmintZero, hredeem]
  change (msg.benv.state.bal ca).toNat + 0 ≤
    (benv.state.bal ca).toNat + 0
  rw [hbal]

/-- An actual call-type spawn aimed away from the current account and at an
already-code-bearing account is a direct CALL/STATICCALL child.  CREATE is
excluded by freshness, while CALLCODE/DELEGATECALL retain the parent's target. -/
theorem Xinst.step_spawn_codeAddress_eq_currentTarget
    {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (hs : Xinst.step sevm devm x = .spawn f rsm)
    (hne : sevm.currentTarget ≠ f.inner.currentTarget)
    (hcode : devm.getCode f.inner.currentTarget ≠ .empty) :
    f.inner.codeAddress = some f.inner.currentTarget := by
  have horig := hs
  cases x with
  | create =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have hfresh := genericCreate.step_spawn_frame hs
          apply False.elim
          apply hcode
          calc
            devm.getCode f.inner.currentTarget =
                f.inner.benv.state.getCode f.inner.currentTarget :=
              (Xinst.step_spawn_getCode horig _).symm
            _ = _ := hfresh.1 _
            _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
  | create2 =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have hfresh := genericCreate.step_spawn_frame hs
          apply False.elim
          apply hcode
          calc
            devm.getCode f.inner.currentTarget =
                f.inner.benv.state.getCode f.inner.currentTarget :=
              (Xinst.step_spawn_getCode horig _).symm
            _ = _ := hfresh.1 _
            _ = .empty := by rw [hfresh.2.1, hfresh.2.2]
  | call =>
      simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | rcases genericCall_step_spawn_exact hs with ⟨rfl, rfl⟩
          rfl
  | callcode =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have htgt := (genericCall.step_spawn_frame hs).2.1
          exact False.elim (hne htgt.symm)
  | delcall =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | have htgt := (genericCall.step_spawn_frame hs).2.1
          exact False.elim (hne htgt.symm)
  | statcall =>
      simp only [Xinst.step, Bind.bind, Except.bind] at hs
      repeat' split at hs
      all_goals simp only [XStep.ofExcept, reduceCtorEq] at hs
      all_goals first
        | cases hs
        | rcases genericCall_step_spawn_exact hs with ⟨rfl, rfl⟩
          rfl

/-- A successful no-slot zero-value call is balance-silent even when WETH10
is both caller and callee.  Empty-code and precompile execution cannot alter
the world beyond message entry. -/
theorem ProcessMessage.ethBound_of_none_value_eq_zero
    {ca : Adr} {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (hzero : msg.value = 0) :
    EthBound ca msg.benv.state post.state [] := by
  rcases ProcessMessage.none_ok_state_cases hprocess with hrollback |
      ⟨benv, htransfer, hpost⟩
  · rw [hrollback]
    exact EthBound.refl ca msg.benv.state
  · have hbal := Msg.benvAfterTransfer_bal_eq_of_value_eq_zero
      hzero htransfer
    rw [hpost]
    unfold EthBound
    simp only [flowActionsEthMint, flowActionsEthRedemption,
      List.map_nil, List.sum_nil, Nat.add_zero]
    rw [hbal]

/-- No-code and precompile recipients are valid accepted redemption targets.
The parent action still pays for the actual value transfer; a self-targeted
empty execution merely leaves additional redemption slack on the right. -/
theorem ProcessMessage.ethBound_of_none_redemption
    {ca : Adr} {msg : Msg} {post : Devm}
    (hprocess : ProcessMessage msg .none (.ok post))
    (hstv : msg.shouldTransferValue = true)
    (hcaller : msg.caller = ca)
    {action : FlowAction} {rawSource : B256}
    {source ethRecipient : Adr}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient msg.value.toNat) :
    EthBound ca msg.benv.state post.state [action] := by
  rcases ProcessMessage.none_ok_state_cases hprocess with hrollback |
      ⟨benv, htransfer, hpost⟩
  · rw [hrollback]
    simp [EthBound, flowActionsEthMint, flowActionsEthRedemption,
      hatom, FlowAtom.ethMint, FlowAtom.ethRedemption]
  · rw [hpost]
    by_cases htarget : msg.currentTarget = ca
    · rcases of_benvAfterTransfer hstv htransfer with
        ⟨debit, hsub, rfl⟩
      have hself :=
        (of_state_transfer_fields
          (callee := msg.currentTarget) hsub).2.2.2.1
      have hbal :
          (debit.addBal msg.currentTarget msg.value).bal ca =
            msg.benv.state.bal ca := by
        rw [← hcaller]
        exact hself (htarget.trans hcaller.symm)
      unfold EthBound
      simp only [flowActionsEthMint, List.map_cons, FlowAtom.ethMint,
        List.map_nil, List.sum_nil, List.sum_cons,
        flowActionsEthRedemption, hatom, FlowAtom.ethRedemption,
        Nat.add_zero]
      change (msg.benv.state.bal ca).toNat ≤
        ((debit.addBal msg.currentTarget msg.value).bal ca).toNat +
          msg.value.toNat
      rw [hbal]
      omega
    · exact (EthStep.of_benvAfterTransfer_redemption
        hstv hcaller htarget hatom htransfer).bound

/-- Recursive interpreter-slot accounting for an internal zero-value call.
Unlike transaction entry, this permits `msg.caller = ca`; zero value makes the
entry balance-preserving and forces any nested ordinary-mint ETH weight to
zero. -/
theorem ProcessMessage.ethBound_of_zeroBodyBound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hzero : msg.value = 0)
    (hbody : ∀ (hcommit : Execution.commits out = true),
      EthBound ca pre.state
        (Execution.committedPost out hcommit).state
        (Exec.bodyEthActions dp ca run hcommit)) :
    EthBound ca msg.benv.state post.state
      (Exec.flowActions dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  by_cases hcommit : Execution.commits out = true
  · have hentry := Exec.entryEthBound_of_value_eq_zero
      (dp := dp) (ca := ca) run htransfer hinit hcommit hzero
    have hbound := hentry.trans (hbody hcommit)
    rw [ProcessMessage.ok_state_eq_committedPost hprocess hcommit]
    simpa only [Frame.ofCall,
      Exec.flowActions_eq_entry_append_body
        (dp := dp) (ca := ca) run hcommit] using hbound
  · have hstate :=
      ProcessMessage.ok_state_eq_of_not_commits hprocess hcommit
    rw [Exec.flowActions_eq_nil_of_not_commits run hcommit, hstate]
    exact EthBound.refl ca msg.benv.state

/-- Apply the proof-indexed recursive body theorem to a concrete internal
zero-value child.  The caller supplies only installed-code and direct-frame
provenance; entry, root freshness, the global sum bound, and rollback are
derived from the retained `ProcessMessage`. -/
theorem ProcessMessage.ethBound_of_zeroCoreSound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hzero : msg.value = 0)
    (childSound : Exec.CoreEthSound dp ca pc sevm pre out)
    (hchildAt : Prog.At (weth10 dp) ca pc sevm pre)
    (hdirect : sevm.currentTarget = ca → sevm.codeAddress = some ca)
    (hsum : sum msg.benv.state.bal < 2 ^ 256) :
    EthBound ca msg.benv.state post.state
      (Exec.flowActions dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  have hsumChild : sum pre.state.bal < 2 ^ 256 := by
    have hnoninc := Msg.benvAfterTransfer_balance_effect htransfer
    have hpreEq := congrArg (fun e : Evm => e.dyna.state.bal) hinit
    dsimp [initEvm, initDevm, Msg.withBenv] at hpreEq
    rw [hpreEq]
    exact lt_of_le_of_lt hnoninc hsum
  have hbody : ∀ (hcommit : Execution.commits out = true),
      EthBound ca pre.state
        (Execution.committedPost out hcommit).state
        (Exec.bodyEthActions dp ca run hcommit) := by
    intro hcommit
    have hpc := congrArg Evm.pc hinit
    have hmem := congrArg (fun e : Evm => e.dyna.memory) hinit
    dsimp [initEvm, initDevm, Msg.withBenv] at hpc hmem
    have hroot : Exec.Frame.IsRoot
        (Exec.Frame.ofRun run hcommit) := ⟨hpc, hmem⟩
    exact childSound run hcommit hchildAt
      (fun htarget => ⟨hroot, hdirect htarget⟩) hsumChild
  exact ProcessMessage.ethBound_of_zeroBodyBound
    run hprocess hzero hbody

/-- Recursive-body wrapper for the accepted value child of a redemption.
The concrete parent action pays for the transfer; the child proof contributes
its exact entry/body action traversal. -/
theorem ProcessMessage.ethBound_of_redemptionCoreSound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hclean : post.error.isSome = false)
    (hstv : msg.shouldTransferValue = true)
    (hcaller : msg.caller = ca)
    {action : FlowAction} {rawSource : B256}
    {source ethRecipient : Adr}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient msg.value.toNat)
    (childSound : Exec.CoreEthSound dp ca pc sevm pre out)
    (hchildAt : Prog.At (weth10 dp) ca pc sevm pre)
    (hdirect : sevm.currentTarget = ca → sevm.codeAddress = some ca)
    (hsum : sum msg.benv.state.bal < 2 ^ 256) :
    EthBound ca msg.benv.state post.state
      (action :: Exec.flowActions dp ca run) := by
  have henter := (RunFrame.some_inv hprocess).1
  rcases Frame.enter_run_inv henter with ⟨benv, htransfer, hinit⟩
  have hsumChild : sum pre.state.bal < 2 ^ 256 := by
    have hnoninc := Msg.benvAfterTransfer_balance_effect htransfer
    have hpreEq := congrArg (fun e : Evm => e.dyna.state.bal) hinit
    dsimp [initEvm, initDevm, Msg.withBenv] at hpreEq
    rw [hpreEq]
    exact lt_of_le_of_lt hnoninc hsum
  have hbody : ∀ (hcommit : Execution.commits out = true),
      EthBound ca pre.state
        (Execution.committedPost out hcommit).state
        (Exec.bodyEthActions dp ca run hcommit) := by
    intro hcommit
    have hpc := congrArg Evm.pc hinit
    have hmem := congrArg (fun e : Evm => e.dyna.memory) hinit
    dsimp [initEvm, initDevm, Msg.withBenv] at hpc hmem
    have hroot : Exec.Frame.IsRoot
        (Exec.Frame.ofRun run hcommit) := ⟨hpc, hmem⟩
    exact childSound run hcommit hchildAt
      (fun htarget => ⟨hroot, hdirect htarget⟩) hsumChild
  exact ProcessMessage.ethBound_of_redemptionBodyBound
    run hprocess hclean hstv hcaller hatom hbody

/-- Resolving a CALL target that is the installed WETH10 address cannot take
the EIP-7702 delegation arm: compiled Blanc code is not a delegation marker.
Thus the concrete child code is the installed runtime itself. -/
theorem resolvedCallCode_eq_installed_of_target_eq
    {dp : DeployParams} {ca target : Adr} {parent : Devm}
    {code : ByteArray} {delegated : Bool}
    (hinstalled : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hresolution :
      (getDelegatedCodeAddress (parent.getCode target) = none ∧
          code = parent.getCode target ∧ delegated = false) ∨
        (∃ delegatedTarget,
          getDelegatedCodeAddress (parent.getCode target) =
            some delegatedTarget ∧
          code = parent.getCode delegatedTarget ∧ delegated = true))
    (htarget : target = ca) :
    some code.toList = Prog.compile (weth10 dp) := by
  subst target
  have hnone :
      getDelegatedCodeAddress (parent.getCode ca) = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hinstalled)]
  rcases hresolution with hdirect |
      ⟨delegatedTarget, hsome, _, _⟩
  · rw [hdirect.2.1]
    exact hinstalled
  · rw [hnone] at hsome
    cases hsome

/-- Execution-authentic accounting for a retained internal zero-value child.
The message boundary supplies exactly the code and direct-call provenance
needed to invoke the strong-depth `CoreEthSound` hypothesis; no transaction
`MsgInv` is assumed for the contract-originated callback. -/
theorem ProcessMessageTrace.ethBound_of_zeroDeeper
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (htargetAddress : msg.currentTarget = ca →
      msg.codeAddress = some ca)
    (hzero : msg.value = 0)
    (hdeeper : ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum parent.state.bal < 2 ^ 256) :
    EthBound ca parent.state post.state
      (trace.retained.flowActions dp ca) := by
  have hsumMsg : sum msg.benv.state.bal < 2 ^ 256 := by
    rw [← hparent]
    exact hsum
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      have hbound := ProcessMessage.ethBound_of_none_value_eq_zero
        (ca := ca) hprocess hzero
      unfold EthBound at hbound ⊢
      rw [hparent]
      exact hbound
  | @some pc sevm pre out run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hprocess).1
      rcases Frame.enter_run_inv henter with
        ⟨benv, htransfer, hevm⟩
      simp only [Frame.ofCall] at htransfer hevm
      have hpreState : pre.state = benv.state := by
        have component :=
          congrArg (fun evm : Evm => evm.dyna.state) hevm
        change pre.state = (initEvm (msg.withBenv benv)).dyna.state
        exact component
      have hsevm : sevm = initSevm (msg.withBenv benv) :=
        congrArg (fun evm : Evm => evm.sta) hevm
      have hpc : pc = 0 := by
        simpa [initEvm] using congrArg (fun evm : Evm => evm.pc) hevm
      have hentryCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        calc
          some (pre.getCode ca).toList =
              some (benv.state.getCode ca).toList := by
            change some (pre.state.getCode ca).toList = _
            rw [hpreState]
          _ = some (msg.benv.state.getCode ca).toList := by
            rw [benvAfterTransfer_ok_getCode htransfer ca]
          _ = some (parent.getCode ca).toList := by
            change some (msg.benv.state.getCode ca).toList =
              some (parent.state.getCode ca).toList
            rw [hparent]
          _ = _ := hcode
      have hat : Prog.At (weth10 dp) ca pc sevm pre := by
        refine ⟨hentryCode, ?_⟩
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        refine ⟨?_, hpc⟩
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using
          htargetCode hmsgTarget
      have hdirect : sevm.currentTarget = ca →
          sevm.codeAddress = some ca := by
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using
          htargetAddress hmsgTarget
      have hdepthChild : sevm.depth < depth := by
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using hdepth
      have childSound : Exec.CoreEthSound dp ca pc sevm pre out :=
        hdeeper pc sevm pre out run hdepthChild hat
      have hbound := ProcessMessage.ethBound_of_zeroCoreSound
        run hprocess hzero childSound hat hdirect hsumMsg
      unfold EthBound at hbound ⊢
      rw [hparent]
      exact hbound

/-- Execution-authentic accounting for the retained value child selected by
a compiled burn prefix.  The action is deliberately supplied by the parent
classifier and is checked against the concrete child message value before the
strong-depth body theorem is used. -/
theorem ProcessMessageTrace.ethBound_of_redemptionDeeper
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {post parent : Devm}
    (trace : ProcessMessageTrace msg (.ok post))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (htargetAddress : msg.currentTarget = ca →
      msg.codeAddress = some ca)
    (hclean : post.error.isSome = false)
    (hstv : msg.shouldTransferValue = true)
    (hcaller : msg.caller = ca)
    {action : FlowAction} {rawSource : B256}
    {source ethRecipient : Adr}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient msg.value.toNat)
    (hdeeper : ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum parent.state.bal < 2 ^ 256) :
    EthBound ca parent.state post.state
      (action :: trace.retained.flowActions dp ca) := by
  have hsumMsg : sum msg.benv.state.bal < 2 ^ 256 := by
    rw [← hparent]
    exact hsum
  rcases trace with ⟨slot, retained, hprocess⟩
  cases retained with
  | none =>
      have hbound := ProcessMessage.ethBound_of_none_redemption
        hprocess hstv hcaller hatom
      unfold EthBound at hbound ⊢
      rw [hparent]
      exact hbound
  | @some pc sevm pre out run =>
      have henter : (Frame.ofCall msg).enter =
          .run ⟨pc, sevm, pre⟩ :=
        (RunFrame.some_inv hprocess).1
      rcases Frame.enter_run_inv henter with
        ⟨benv, htransfer, hevm⟩
      simp only [Frame.ofCall] at htransfer hevm
      have hpreState : pre.state = benv.state := by
        have component :=
          congrArg (fun evm : Evm => evm.dyna.state) hevm
        change pre.state = (initEvm (msg.withBenv benv)).dyna.state
        exact component
      have hsevm : sevm = initSevm (msg.withBenv benv) :=
        congrArg (fun evm : Evm => evm.sta) hevm
      have hpc : pc = 0 := by
        simpa [initEvm] using congrArg (fun evm : Evm => evm.pc) hevm
      have hentryCode : some (pre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        calc
          some (pre.getCode ca).toList =
              some (benv.state.getCode ca).toList := by
            change some (pre.state.getCode ca).toList = _
            rw [hpreState]
          _ = some (msg.benv.state.getCode ca).toList := by
            rw [benvAfterTransfer_ok_getCode htransfer ca]
          _ = some (parent.getCode ca).toList := by
            change some (msg.benv.state.getCode ca).toList =
              some (parent.state.getCode ca).toList
            rw [hparent]
          _ = _ := hcode
      have hat : Prog.At (weth10 dp) ca pc sevm pre := by
        refine ⟨hentryCode, ?_⟩
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        refine ⟨?_, hpc⟩
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using
          htargetCode hmsgTarget
      have hdirect : sevm.currentTarget = ca →
          sevm.codeAddress = some ca := by
        intro htarget
        have hmsgTarget : msg.currentTarget = ca := by
          rw [hsevm] at htarget
          simpa [initSevm, Msg.withBenv] using htarget
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using
          htargetAddress hmsgTarget
      have hdepthChild : sevm.depth < depth := by
        rw [hsevm]
        simpa [initSevm, Msg.withBenv] using hdepth
      have childSound : Exec.CoreEthSound dp ca pc sevm pre out :=
        hdeeper pc sevm pre out run hdepthChild hat
      have hbound := ProcessMessage.ethBound_of_redemptionCoreSound
        run hprocess hclean hstv hcaller hatom childSound hat hdirect
          hsumMsg
      unfold EthBound at hbound ⊢
      rw [hparent]
      exact hbound

/-- The ETH accounting payload attached to one exact retained zero-value
`CALL` occurrence.  The `StepRun` and `ProcessMessageTrace` share the same
proof-indexed slot, so a chronological cursor can splice `bound` into the
enclosing frame without re-identifying the child by endpoint alone. -/
structure ZeroValueCallEthSegment
    (dp : DeployParams) (ca : Adr) (e : Sevm)
    (callPre callPost : Devm) : Type where
  pc : Nat
  msg : Msg
  child : Devm
  trace : ProcessMessageTrace msg (.ok child)
  step : Ninst.StepRun pc e callPre Ninst.call trace.slot (.ok callPost)
  clean : child.error.isSome = false
  bound : EthBound ca callPre.state callPost.state
    (trace.retained.flowActions dp ca)

/-- A zero-value call segment together with the balance-silent parent prefix
and suffix surrounding that exact instruction. -/
structure ZeroValueCallbackEthSegment
    (dp : DeployParams) (ca : Adr) (e : Sevm)
    (pre post : Devm) : Type where
  callPre : Devm
  callPost : Devm
  call : ZeroValueCallEthSegment dp ca e callPre callPost
  preBalance : Devm.getBal pre = Devm.getBal callPre
  postBalance : Devm.getBal post = Devm.getBal callPost

/-- The parent prefix and suffix around a zero-value callback contribute no
additional ETH weight. -/
theorem ZeroValueCallbackEthSegment.bound
    {dp : DeployParams} {ca : Adr} {e : Sevm} {pre post : Devm}
    (segment : ZeroValueCallbackEthSegment dp ca e pre post) :
    EthBound ca pre.state post.state
      (segment.call.trace.retained.flowActions dp ca) := by
  rcases segment with
    ⟨callPre, callPost, call, hpreBalance, hpostBalance⟩
  have hprefix : EthBound ca pre.state callPre.state [] :=
    (EthStep.silent (congrFun hpreBalance ca).symm).bound
  have hsuffix : EthBound ca callPost.state post.state [] :=
    (EthStep.silent (congrFun hpostBalance ca)).bound
  simpa only [List.nil_append, List.append_nil] using
    hprefix.trans (call.bound.trans hsuffix)

/-- A root action whose atom has no ETH weight can be restored in front of an
already-accounted chronological child ledger. -/
theorem EthBound.cons_of_atom_eth_eq_zero
    {ca : Adr} {pre post : State} {actions : List FlowAction}
    {action : FlowAction}
    (bound : EthBound ca pre post actions)
    (hmint : action.atom.ethMint = 0)
    (hredemption : action.atom.ethRedemption = 0) :
    EthBound ca pre post (action :: actions) := by
  unfold EthBound at bound ⊢
  simp only [flowActionsEthMint, flowActionsEthRedemption,
    List.map_cons, List.sum_cons]
  rw [hmint, hredemption, Nat.zero_add]
  simpa only [flowActionsEthMint, flowActionsEthRedemption,
    Nat.zero_add] using bound

/-- Frame-oriented spelling of the body/root/descendant split. -/
theorem Exec.Frame.bodyEthActions_eq
    {dp : DeployParams} {ca : Adr} (frame : Exec.Frame) :
    Exec.bodyEthActions dp ca frame.run frame.committed =
      flowActionBodyEthActions (frame.flowAction? dp ca) ++
        frame.descendantFlowActions dp ca := by
  cases frame
  rfl

/-- The retained flash-borrower callback is an exact zero-value ETH segment.
The raw functional boundary provides delegation resolution and the concrete
message; the strong-depth hypothesis accounts arbitrary committed callback
and reentrant WETH10 execution. -/
theorem RawFlashCallbackStepBoundary.zeroValueCallEthSegment
    {dp : DeployParams} {ca self receiver : Adr}
    {e : Sevm} {amount inputSize : B256} {input : Bytes}
    {pre post : Devm}
    (callback : RawFlashCallbackStepBoundary e self receiver amount
      inputSize input pre post)
    (hinstalled : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreEthSound dp ca pc sevm childPre out))
    (hsum : sum pre.state.bal < 2 ^ 256) :
    Nonempty (ZeroValueCallEthSegment dp ca e pre post) := by
  rcases callback with
    ⟨parent, child, xl, delegated, code, gasWord, avail, pc,
      hstep, hdepth, _hstack, _hpref, hparentState, _hmemory,
      _hlogs, _houtput, hresolution, hfilled, hprocess, hclean,
      _hlength, _hmagic, _hresume, hpostState, _hreturnData,
      _hpostStack, _hpostLogs, _hpostOutput⟩
  let msg :=
    callMsg e parent (min gasWord.toNat (except64th avail)) 0
      self receiver receiver true false input code delegated
  rcases exists_retainedXlot_of_filled hfilled with ⟨retained⟩
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hparent : pre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    simp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have hreceiver : receiver = ca := by
      simpa only [msg, callMsg] using htarget
    simpa only [msg, callMsg] using
      resolvedCallCode_eq_installed_of_target_eq
        hinstalled hresolution hreceiver
  have htargetAddress : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have hreceiver : receiver = ca := by
      simpa only [msg, callMsg] using htarget
    simp only [msg, callMsg, hreceiver]
  have hzero : msg.value = 0 := by
    simp only [msg, callMsg]
  have hbound := trace.ethBound_of_zeroDeeper hparent hmsgDepth
    hinstalled htargetCode htargetAddress hzero hdeeper hsum
  have hboundPost : EthBound ca pre.state post.state
      (trace.retained.flowActions dp ca) := by
    unfold EthBound at hbound ⊢
    rw [hpostState]
    exact hbound
  exact ⟨⟨pc, msg, child, trace,
    by simpa only [trace] using hstep, hclean, hboundPost⟩⟩

/-- Whole-boundary form of the flash callback segment. -/
theorem RawFlashCallbackStepBoundary.zeroValueCallbackEthSegment
    {dp : DeployParams} {ca self receiver : Adr}
    {e : Sevm} {amount inputSize : B256} {input : Bytes}
    {pre post : Devm}
    (callback : RawFlashCallbackStepBoundary e self receiver amount
      inputSize input pre post)
    (hinstalled : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreEthSound dp ca pc sevm childPre out))
    (hsum : sum pre.state.bal < 2 ^ 256) :
    Nonempty (ZeroValueCallbackEthSegment dp ca e pre post) := by
  rcases callback.zeroValueCallEthSegment hinstalled hdeeper hsum with
    ⟨call⟩
  exact ⟨⟨pre, post, call, rfl, rfl⟩⟩

/-- Indexed flash-callback ETH accounting using the exact retained child
selected by the enclosing compiled chronology. -/
theorem RawFlashCallbackIndexedStepBoundary.zeroValueCallbackEthSegment
    {dp : DeployParams} {ca self receiver : Adr}
    {e : Sevm} {amount inputSize : B256} {input : Bytes}
    {pre post parent child : Devm} {xl : Xlot} {pc : Nat}
    (callback : RawFlashCallbackIndexedStepBoundary e self receiver amount
      inputSize input pre post parent child xl pc)
    (retained : RetainedXlot xl)
    (hinstalled : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreEthSound dp ca pc sevm childPre out))
    (hsum : sum pre.state.bal < 2 ^ 256) :
    ∃ segment : ZeroValueCallbackEthSegment dp ca e pre post,
      segment.call.trace.retained.flowActions dp ca =
        retained.flowActions dp ca := by
  rcases callback with
    ⟨delegated, code, gasWord, avail, hstep, hdepth, _hstack, _hpref,
      hparentState, _hparentMemory, _hparentLogs, _hparentOutput,
      hresolution, _hfilled, hprocess, hclean, _hlength, _hmagic,
      _hresume, hpostState, _hreturnData, _hpostStack, _hpostLogs,
      _hpostOutput⟩
  let msg :=
    callMsg e parent (min gasWord.toNat (except64th avail)) 0
      self receiver receiver true false input code delegated
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hparent : pre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    simp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have hreceiver : receiver = ca := by
      simpa only [msg, callMsg] using htarget
    simpa only [msg, callMsg] using
      resolvedCallCode_eq_installed_of_target_eq
        hinstalled hresolution hreceiver
  have htargetAddress : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have hreceiver : receiver = ca := by
      simpa only [msg, callMsg] using htarget
    simp only [msg, callMsg, hreceiver]
  have hzero : msg.value = 0 := by
    simp only [msg, callMsg]
  have hbound := trace.ethBound_of_zeroDeeper hparent hmsgDepth
    hinstalled htargetCode htargetAddress hzero hdeeper hsum
  have hboundPost : EthBound ca pre.state post.state
      (trace.retained.flowActions dp ca) := by
    unfold EthBound at hbound ⊢
    rw [hpostState]
    exact hbound
  let callSegment : ZeroValueCallEthSegment dp ca e pre post :=
    ⟨pc, msg, child, trace, by simpa only [trace] using hstep,
      hclean, hboundPost⟩
  exact ⟨⟨pre, post, callSegment, rfl, rfl⟩, rfl⟩

/-- The raw ERC-677 callback, including its Boolean-return continuation, is
an exact zero-value callback ETH segment. -/
theorem RawTokenCallbackStepBoundary.zeroValueCallbackEthSegment
    {dp : DeployParams} {ca self target : Adr}
    {e : Sevm} {rawTarget sel value tailLen inputSize : B256}
    {tail input : Bytes} {pre post : Devm}
    (callback : RawTokenCallbackStepBoundary dp e self target rawTarget
      sel value tailLen inputSize tail input pre post)
    (hinstalled : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreEthSound dp ca pc sevm childPre out))
    (hsum : sum pre.state.bal < 2 ^ 256) :
    Nonempty (ZeroValueCallbackEthSegment dp ca e pre post) := by
  rcases callback with
    ⟨_htarget, _hsize, callPre, callPost, parent, child, xl,
      delegated, code, gasWord, avail, pc, hstep, hdepth, _hstack,
      _hinput, _hreads, _hstor, hpreBalance, hpreCode, _hlogs,
      _houtput, hparentState, _hparentMemory, _hparentLogs,
      _hparentOutput, hresolution, hfilled, hprocess, hclean,
      _hresume, hcallPostState, _hreturnData, _hmemory,
      _hcallPostStack, hbool⟩
  let msg :=
    callMsg e parent (min gasWord.toNat (except64th avail)) 0
      self target target true false input code delegated
  rcases exists_retainedXlot_of_filled hfilled with ⟨retained⟩
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hinstalledCall : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hpreCode ca]
    exact hinstalled
  have hparent : callPre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    simp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have htarget' : target = ca := by
      simpa only [msg, callMsg] using htarget
    simpa only [msg, callMsg] using
      resolvedCallCode_eq_installed_of_target_eq
        hinstalledCall hresolution htarget'
  have htargetAddress : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have htarget' : target = ca := by
      simpa only [msg, callMsg] using htarget
    simp only [msg, callMsg, htarget']
  have hzero : msg.value = 0 := by
    simp only [msg, callMsg]
  have hsumCall : sum callPre.state.bal < 2 ^ 256 := by
    change sum (Devm.getBal callPre) < 2 ^ 256
    rw [← hpreBalance]
    exact hsum
  have hbound := trace.ethBound_of_zeroDeeper hparent hmsgDepth
    hinstalledCall htargetCode htargetAddress hzero hdeeper hsumCall
  have hboundCall : EthBound ca callPre.state callPost.state
      (trace.retained.flowActions dp ca) := by
    unfold EthBound at hbound ⊢
    rw [hcallPostState]
    exact hbound
  let callSegment : ZeroValueCallEthSegment dp ca e callPre callPost :=
    ⟨pc, msg, child, trace, by simpa only [trace] using hstep,
      hclean, hboundCall⟩
  have hpostBalance : Devm.getBal post = Devm.getBal callPost :=
    (of_run_call_boolReturn_preserves_fields dp hbool).2.1.symm
  exact ⟨⟨callPre, callPost, callSegment, hpreBalance,
    hpostBalance⟩⟩

/-- Indexed ERC-677 callback ETH accounting using the retained child selected
by the enclosing compiled execution. -/
theorem RawTokenCallbackIndexedStepBoundary.zeroValueCallbackEthSegment
    {dp : DeployParams} {ca self target : Adr}
    {e : Sevm} {rawTarget sel value tailLen inputSize : B256}
    {tail input : Bytes} {pre post callPre callPost parent child : Devm}
    {xl : Xlot} {pc : Nat}
    (callback : RawTokenCallbackIndexedStepBoundary dp e self target rawTarget
      sel value tailLen inputSize tail input pre post callPre callPost parent
      child xl pc)
    (retained : RetainedXlot xl)
    (hinstalled : some (pre.getCode ca).toList =
      Prog.compile (weth10 dp))
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreEthSound dp ca pc sevm childPre out))
    (hsum : sum pre.state.bal < 2 ^ 256) :
    ∃ segment : ZeroValueCallbackEthSegment dp ca e pre post,
      segment.call.trace.retained.flowActions dp ca =
        retained.flowActions dp ca := by
  rcases callback with
    ⟨_htarget, _hsize, delegated, code, gasWord, avail, hstep, hdepth,
      _hstack, _hinput, _hreads, _hstor, hpreBalance, hpreCode, _hlogs,
      _houtput, hparentState, _hparentMemory, _hparentLogs,
      _hparentOutput, hresolution, _hfilled, hprocess, hclean,
      _hresume, hcallPostState, _hreturnData, _hmemory,
      _hcallPostStack, hbool⟩
  let msg :=
    callMsg e parent (min gasWord.toNat (except64th avail)) 0
      self target target true false input code delegated
  let trace : ProcessMessageTrace msg (.ok child) :=
    ⟨xl, retained, by simpa only [msg] using hprocess⟩
  have hinstalledCall : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hpreCode ca]
    exact hinstalled
  have hparent : callPre.state = msg.benv.state := by
    simpa only [msg, callMsg] using hparentState.symm
  have hmsgDepth : msg.depth < e.depth := by
    simp only [msg, callMsg]
    omega
  have htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp) := by
    intro htarget
    have htarget' : target = ca := by
      simpa only [msg, callMsg] using htarget
    simpa only [msg, callMsg] using
      resolvedCallCode_eq_installed_of_target_eq
        hinstalledCall hresolution htarget'
  have htargetAddress : msg.currentTarget = ca →
      msg.codeAddress = some ca := by
    intro htarget
    have htarget' : target = ca := by
      simpa only [msg, callMsg] using htarget
    simp only [msg, callMsg, htarget']
  have hzero : msg.value = 0 := by
    simp only [msg, callMsg]
  have hsumCall : sum callPre.state.bal < 2 ^ 256 := by
    change sum (Devm.getBal callPre) < 2 ^ 256
    rw [← hpreBalance]
    exact hsum
  have hbound := trace.ethBound_of_zeroDeeper hparent hmsgDepth
    hinstalledCall htargetCode htargetAddress hzero hdeeper hsumCall
  have hboundCall : EthBound ca callPre.state callPost.state
      (trace.retained.flowActions dp ca) := by
    unfold EthBound at hbound ⊢
    rw [hcallPostState]
    exact hbound
  let callSegment : ZeroValueCallEthSegment dp ca e callPre callPost :=
    ⟨pc, msg, child, trace, by simpa only [trace] using hstep,
      hclean, hboundCall⟩
  have hpostBalance : Devm.getBal post = Devm.getBal callPost :=
    (of_run_call_boolReturn_preserves_fields dp hbool).2.1.symm
  exact ⟨⟨callPre, callPost, callSegment, hpreBalance,
    hpostBalance⟩, rfl⟩

/-- A retained redemption child may be transported to the compiled success
guard endpoint without exposing the enclosing accepted-CALL record. -/
theorem ProcessMessageTrace.redemptionEthBound_to_guard
    {dp : DeployParams} {ca : Adr} {depth : Nat}
    {msg : Msg} {child parent guardPost : Devm}
    (trace : ProcessMessageTrace msg (.ok child))
    (hparent : parent.state = msg.benv.state)
    (hdepth : msg.depth < depth)
    (hcode : some (parent.getCode ca).toList =
      Prog.compile (weth10 dp))
    (htargetCode : msg.currentTarget = ca →
      some msg.code.toList = Prog.compile (weth10 dp))
    (htargetAddress : msg.currentTarget = ca →
      msg.codeAddress = some ca)
    (hclean : child.error.isSome = false)
    (hstv : msg.shouldTransferValue = true)
    (hcaller : msg.caller = ca)
    {action : FlowAction} {rawSource : B256}
    {source ethRecipient : Adr}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient msg.value.toNat)
    (hdeeper : ForallDeeperAt depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum parent.state.bal < 2 ^ 256)
    (hguard : guardPost.state = child.state) :
    EthBound ca parent.state guardPost.state
      (action :: trace.retained.flowActions dp ca) := by
  have bound := trace.ethBound_of_redemptionDeeper
    hparent hdepth hcode htargetCode htargetAddress hclean hstv hcaller
      hatom hdeeper hsum
  rw [hguard]
  exact bound

/-- Message-shape facts projected from an accepted value `CALL`.  Keeping this
separate prevents the recursive ETH theorem from elaborating the full raw
CALL witness and its delegation proof in one declaration. -/
structure AcceptedValueCallTrace.RedemptionMessageFacts
    (dp : DeployParams) (ca : Adr) {e : Sevm}
    {target value : B256} {callPre guardPost : Devm}
    (trace : AcceptedValueCallTrace e target value callPre guardPost) : Prop where
  parent : callPre.state = trace.childMessage.benv.state
  depth : trace.childMessage.depth < e.depth
  targetCode : trace.childMessage.currentTarget = ca →
    some trace.childMessage.code.toList = Prog.compile (weth10 dp)
  targetAddress : trace.childMessage.currentTarget = ca →
    trace.childMessage.codeAddress = some ca
  shouldTransferValue : trace.childMessage.shouldTransferValue = true
  value : trace.childMessage.value = value
  caller : trace.childMessage.caller = ca

theorem AcceptedValueCallTrace.redemptionMessageFacts
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {target value : B256} {callPre guardPost : Devm}
    (trace : AcceptedValueCallTrace e target value callPre guardPost)
    (hself : e.currentTarget = ca)
    (hinstalled : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp)) :
    trace.RedemptionMessageFacts dp ca := by
  constructor
  · rw [trace.childMessage_eq]
    simpa only [callMsg] using trace.parent_state.symm
  · rw [trace.childMessage_eq]
    simp only [callMsg]
    exact Nat.sub_lt trace.depth_pos (by decide)
  · intro htarget
    rw [trace.childMessage_eq] at htarget ⊢
    have htarget' : target.toAdr = ca := by
      simpa only [callMsg] using htarget
    simpa only [callMsg] using
      resolvedCallCode_eq_installed_of_target_eq
        hinstalled trace.delegation_resolution htarget'
  · intro htarget
    rw [trace.childMessage_eq] at htarget ⊢
    have htarget' : target.toAdr = ca := by
      simpa only [callMsg] using htarget
    simp only [callMsg, htarget']
  · rw [trace.childMessage_eq]
    rfl
  · rw [trace.childMessage_eq]
    rfl
  · rw [trace.childMessage_eq]
    simp only [callMsg]
    exact hself

/-- Opaque wrapper around the recursively proved redemption inequality. -/
structure AcceptedValueCallTrace.RedemptionEthWitness
    (dp : DeployParams) (ca : Adr) {e : Sevm}
    {target value : B256} {callPre guardPost : Devm}
    (action : FlowAction)
    (trace : AcceptedValueCallTrace e target value callPre guardPost) : Prop where
  bound : EthBound ca callPre.state guardPost.state
    (action :: trace.retained.retained.flowActions dp ca)

/-- The accepted value child retained by a compiled burn prefix pays for the
parent redemption action, while arbitrary committed reentrancy is accounted
by the strong-depth hypothesis. -/
theorem AcceptedValueCallTrace.redemptionEthBound
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {target value : B256} {callPre guardPost : Devm}
    (trace : AcceptedValueCallTrace e target value callPre guardPost)
    (hself : e.currentTarget = ca)
    (hinstalled : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp))
    {action : FlowAction} {rawSource : B256}
    {source ethRecipient : Adr}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient value.toNat)
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreEthSound dp ca pc sevm childPre out))
    (hsum : sum callPre.state.bal < 2 ^ 256) :
    trace.RedemptionEthWitness dp ca action := by
  rcases trace.redemptionMessageFacts hself hinstalled with
    ⟨hparent, hdepth, htargetCode, htargetAddress, hstv, hvalue,
      hcaller⟩
  have hatomMessage : action.atom =
      .redemption rawSource source ethRecipient
        trace.childMessage.value.toNat := by
    rw [hvalue]
    exact hatom
  exact ⟨ProcessMessageTrace.redemptionEthBound_to_guard
    (dp := dp) (ca := ca) (depth := e.depth) (parent := callPre)
    trace.retained hparent hdepth hinstalled htargetCode htargetAddress
      trace.child_clean hstv hcaller hatomMessage hdeeper hsum
        trace.guard_state⟩

/-- An exact accepted value-CALL trace paired with its recursively proved
redemption-labelled ETH segment. -/
structure AcceptedRedemptionEthSegment
    (dp : DeployParams) (ca : Adr) (e : Sevm) (action : FlowAction)
    (callPre guardPost : Devm) : Type where
  target : B256
  value : B256
  trace : AcceptedValueCallTrace e target value callPre guardPost
  bodyActions : action.bodyEthActions = [action]
  bound : EthBound ca callPre.state guardPost.state
    (action :: trace.retained.retained.flowActions dp ca)

/-- A compiled burn prefix yields the exact accepted redemption segment; no
endpoint equation or conservation premise is supplied. -/
theorem BurnCallPrefix.acceptedRedemptionEthSegment
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {pre callPre guardPost : Devm}
    {owner : Adr} {amount target : B256}
    (burn : BurnCallPrefix e pre callPre guardPost owner amount target)
    (hself : e.currentTarget = ca)
    (hinstalled : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp))
    {action : FlowAction} {rawSource : B256}
    {source ethRecipient : Adr}
    (hatom : action.atom =
      .redemption rawSource source ethRecipient amount.toNat)
    (hdeeper : ForallDeeperAt e.depth ca (weth10 dp)
      (fun pc sevm childPre out _ =>
        Exec.CoreEthSound dp ca pc sevm childPre out))
    (hsum : sum callPre.state.bal < 2 ^ 256) :
    Nonempty (AcceptedRedemptionEthSegment dp ca e action
      callPre guardPost) := by
  rcases exists_burnCallPrefixTrace burn with ⟨trace⟩
  have witness := trace.redemptionEthBound hself hinstalled hatom hdeeper hsum
  exact ⟨⟨target, amount, trace,
    by simp [FlowAction.bodyEthActions, hatom],
    witness.bound⟩⟩

/-- A complete redemption body segment includes only balance-silent parent
code before and after the accepted value child. -/
structure RedemptionEthSegment
    (dp : DeployParams) (ca : Adr) (e : Sevm) (action : FlowAction)
    (pre post : Devm) : Type where
  callPre : Devm
  guardPost : Devm
  accepted : AcceptedRedemptionEthSegment dp ca e action callPre guardPost
  preBalance : Devm.getBal pre = Devm.getBal callPre
  postBalance : Devm.getBal post = Devm.getBal guardPost

theorem RedemptionEthSegment.bound
    {dp : DeployParams} {ca : Adr} {e : Sevm} {action : FlowAction}
    {pre post : Devm}
    (segment : RedemptionEthSegment dp ca e action pre post) :
    EthBound ca pre.state post.state
      (action :: segment.accepted.trace.retained.retained.flowActions
        dp ca) := by
  rcases segment with
    ⟨callPre, guardPost, accepted, hpreBalance, hpostBalance⟩
  have hprefix : EthBound ca pre.state callPre.state [] :=
    (EthStep.silent (congrFun hpreBalance ca).symm).bound
  have hsuffix : EthBound ca guardPost.state post.state [] :=
    (EthStep.silent (congrFun hpostBalance ca)).bound
  simpa only [List.nil_append, List.append_nil] using
    hprefix.trans (accepted.bound.trans hsuffix)

/-- Operational ETH compositions for every flow-producing WETH10 body shape.
The constructors retain exact callback/redemption traces and accept only
chronology equations for the proof-indexed descendant ledger. -/
inductive RichBodyEthAccounting
    (dp : DeployParams) (ca : Adr) (e : Sevm)
    (pre post : Devm) (action : FlowAction)
    (descendants : List FlowAction) : Prop
  | mintSilent
      {rawRecipient : B256} {recipient : Adr} {amount : Nat}
      (atom : action.atom = .ordinaryMint rawRecipient recipient amount)
      (balance : Devm.getBal post = Devm.getBal pre)
      (chronology : descendants = [])
  | mintCallback
      {rawRecipient : B256} {recipient : Adr} {amount : Nat}
      (atom : action.atom = .ordinaryMint rawRecipient recipient amount)
      (callback : ZeroValueCallbackEthSegment dp ca e pre post)
      (chronology : descendants =
        callback.call.trace.retained.flowActions dp ca)
  | zeroSilent
      (bodyActions : action.bodyEthActions = [action])
      (mintZero : action.atom.ethMint = 0)
      (redemptionZero : action.atom.ethRedemption = 0)
      (balance : Devm.getBal post = Devm.getBal pre)
      (chronology : descendants = [])
  | zeroCallback
      (bodyActions : action.bodyEthActions = [action])
      (mintZero : action.atom.ethMint = 0)
      (redemptionZero : action.atom.ethRedemption = 0)
      (callback : ZeroValueCallbackEthSegment dp ca e pre post)
      (chronology : descendants =
        callback.call.trace.retained.flowActions dp ca)
  | redemption
      (segment : RedemptionEthSegment dp ca e action pre post)
      (chronology : descendants =
        segment.accepted.trace.retained.retained.flowActions dp ca)
  | redemptionThenCallback
      {middle : Devm}
      (redemption : RedemptionEthSegment dp ca e action pre middle)
      (callback : ZeroValueCallbackEthSegment dp ca e middle post)
      (chronology : descendants =
        redemption.accepted.trace.retained.retained.flowActions dp ca ++
          callback.call.trace.retained.flowActions dp ca)

/-- A rich operational body composition proves precisely the body-side list:
ordinary mints are omitted because their ETH was counted at message entry;
all other root actions remain in front of the chronological descendants. -/
theorem RichBodyEthAccounting.bound
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {pre post : Devm} {action : FlowAction}
    {descendants : List FlowAction}
    (accounting : RichBodyEthAccounting dp ca e pre post action descendants) :
    EthBound ca pre.state post.state
      (action.bodyEthActions ++ descendants) := by
  cases accounting with
  | mintSilent atom balance chronology =>
      subst descendants
      have bound : EthBound ca pre.state post.state [] :=
        (EthStep.silent (congrFun balance ca)).bound
      simpa [FlowAction.bodyEthActions, atom] using bound
  | mintCallback atom callback chronology =>
      rw [chronology]
      simpa [FlowAction.bodyEthActions, atom] using callback.bound
  | zeroSilent bodyActions mintZero redemptionZero balance chronology =>
      subst descendants
      have bound : EthBound ca pre.state post.state [] :=
        (EthStep.silent (congrFun balance ca)).bound
      have rootBound := bound.cons_of_atom_eth_eq_zero
        mintZero redemptionZero
      simpa only [bodyActions, List.singleton_append,
        List.append_nil] using rootBound
  | zeroCallback bodyActions mintZero redemptionZero callback chronology =>
      rw [chronology]
      have rootBound := callback.bound.cons_of_atom_eth_eq_zero
        mintZero redemptionZero
      simpa only [bodyActions, List.singleton_append] using rootBound
  | redemption segment chronology =>
      rw [chronology]
      simpa only [segment.accepted.bodyActions,
        List.singleton_append] using segment.bound
  | redemptionThenCallback redemption callback chronology =>
      rw [chronology]
      have combined := redemption.bound.trans callback.bound
      simpa only [redemption.accepted.bodyActions,
        List.singleton_append, List.cons_append,
        List.nil_append] using combined

/-- Operational ETH compositions for public bodies with no root flow action.
Besides the standard generated `CALL` callback, `staticCallback` retains an
exact recursive `STATICCALL` bound between balance-silent parent segments. -/
inductive NoFlowBodyEthAccounting
    (dp : DeployParams) (ca : Adr) (e : Sevm)
    (pre post : Devm) (descendants : List FlowAction) : Prop
  | silent
      (balance : Devm.getBal post = Devm.getBal pre)
      (chronology : descendants = [])
  | callback
      (segment : ZeroValueCallbackEthSegment dp ca e pre post)
      (chronology : descendants =
        segment.call.trace.retained.flowActions dp ca)
  | staticCallback
      {callPre callPost : Devm} {children : List FlowAction}
      (preBalance : Devm.getBal pre = Devm.getBal callPre)
      (child : EthBound ca callPre.state callPost.state children)
      (postBalance : Devm.getBal post = Devm.getBal callPost)
      (chronology : descendants = children)

theorem NoFlowBodyEthAccounting.bound
    {dp : DeployParams} {ca : Adr} {e : Sevm}
    {pre post : Devm} {descendants : List FlowAction}
    (accounting : NoFlowBodyEthAccounting dp ca e pre post descendants) :
    EthBound ca pre.state post.state descendants := by
  cases accounting with
  | silent balance chronology =>
      subst descendants
      exact (EthStep.silent (congrFun balance ca)).bound
  | callback segment chronology =>
      rw [chronology]
      exact segment.bound
  | staticCallback preBalance child postBalance chronology =>
      rw [chronology]
      have prefixBound : EthBound ca pre.state _ [] :=
        (EthStep.silent (congrFun preBalance ca).symm).bound
      have suffixBound : EthBound ca _ post.state [] :=
        (EthStep.silent (congrFun postBalance ca)).bound
      simpa only [List.nil_append, List.append_nil] using
        prefixBound.trans (child.trans suffixBound)

/-- A filled CALL child contributes actions exactly when the complete call
settlement commits.  If settlement does not commit, the child's world is the
saved message world and the retained action list is empty. -/
theorem ProcessMessage.ethBound_of_settledBodyBound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessMessage msg (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hcaller : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hval0 : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (hsum : sum msg.benv.state.bal < 2 ^ 256)
    (hbody : ∀ (hcommit : Execution.commits out = true),
      EthBound ca pre.state
        (Execution.committedPost out hcommit).state
        (Exec.bodyEthActions dp ca run hcommit)) :
    EthBound ca msg.benv.state post.state
      (if Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCall msg) out = true
       then Exec.flowActions dp ca run else []) := by
  by_cases hsettle :
      Blanc.Weth10.Frame.settlementCommits
        (Frame.ofCall msg) out = true
  · rw [if_pos hsettle]
    exact ProcessMessage.ethBound_of_bodyBound run hprocess
      hcaller hval0 hsum hbody
  · rw [if_neg hsettle]
    have hset := (RunFrame.some_inv hprocess).2
    have herr : post.error.isSome = true := by
      have hnone : post.error.isNone ≠ true := by
        intro hnone
        apply hsettle
        unfold Blanc.Weth10.Frame.settlementCommits
        rw [← hset]
        exact hnone
      cases he : post.error <;> simp_all
    rw [(ProcessMessage.rollback_of_error hprocess herr).1]
    exact EthBound.refl ca msg.benv.state

/-- CREATE's outer code-deposit settlement is part of the same retention
decision.  Clean settlement reduces to the inner message bound and preserves
balances; every noncommitting settlement restores the outer saved world. -/
theorem ProcessCreateMessage.ethBound_of_settledBodyBound
    {dp : DeployParams} {ca : Adr}
    {msg : Msg} {post : Devm} {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hprocess :
      ProcessCreateMessage msg
        (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (hcaller : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (hval0 : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (hsum : sum msg.benv.state.bal < 2 ^ 256)
    (hbody : ∀ (hcommit : Execution.commits out = true),
      EthBound ca pre.state
        (Execution.committedPost out hcommit).state
        (Exec.bodyEthActions dp ca run hcommit)) :
    EthBound ca msg.benv.state post.state
      (if Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCreate msg) out = true
       then Exec.flowActions dp ca run else []) := by
  by_cases hsettle :
      Blanc.Weth10.Frame.settlementCommits
        (Frame.ofCreate msg) out = true
  · rw [if_pos hsettle]
    have hset := (RunFrame.some_inv hprocess).2
    have hnone : post.error.isNone = true := by
      unfold Blanc.Weth10.Frame.settlementCommits at hsettle
      rw [← hset] at hsettle
      exact hsettle
    have herr : post.error.isSome = false := by
      cases he : post.error <;> simp_all
    rcases ProcessCreateMessage.ok_state_eq_inner_of_no_error
      hprocess herr with ⟨inner, hinner, hpost⟩
    have hcallerSeed :
        (processCreateMessage.msg msg).shouldTransferValue = true →
          (processCreateMessage.msg msg).caller ≠ ca := by
      simpa [processCreateMessage.msg, Msg.withBenv] using hcaller
    have hval0Seed :
        (processCreateMessage.msg msg).shouldTransferValue = false →
          (processCreateMessage.msg msg).currentTarget = ca →
          (processCreateMessage.msg msg).value = 0 := by
      simpa [processCreateMessage.msg, Msg.withBenv] using hval0
    have hsumSeed :
        sum (processCreateMessage.msg msg).benv.state.bal < 2 ^ 256 := by
      rw [processCreateMessage_msg_bal_eq]
      exact hsum
    have hbound := ProcessMessage.ethBound_of_bodyBound
      run hinner hcallerSeed hval0Seed hsumSeed hbody
    unfold EthBound at hbound ⊢
    rw [hpost, ← congrFun (processCreateMessage_msg_bal_eq msg) ca]
    exact hbound
  · rw [if_neg hsettle]
    have hset := (RunFrame.some_inv hprocess).2
    have herr : post.error.isSome = true := by
      have hnone : post.error.isNone ≠ true := by
        intro hnone
        apply hsettle
        unfold Blanc.Weth10.Frame.settlementCommits
        rw [← hset]
        exact hnone
      cases he : post.error <;> simp_all
    rw [ProcessCreateMessage.rollback_of_error hprocess herr]
    exact EthBound.refl ca msg.benv.state

/-- Recursive CALL transport for a foreign parent.  Message entry, child body,
settlement rollback, and resume are all tied to the concrete filled slot. -/
theorem GenericCall.foreignSomeEthBound
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {delegated : Bool}
    {cevm : Evm} {raw : Execution} {post : Devm}
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code delegated
      (.some ⟨cevm, raw⟩) (.ok post))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (childSound : Exec.CoreEthSound dp ca
      cevm.pc cevm.sta cevm.dyna raw)
    (hchildAt : Prog.At (weth10 dp) ca
      cevm.pc cevm.sta cevm.dyna)
    (hdirect : cevm.sta.currentTarget = ca →
      cevm.sta.codeAddress = some ca)
    (hcaller : stv = true → caller ≠ ca)
    (hval0 : stv = false → target = ca → value = 0)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state
      (if Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCall
            (callMsg sevm (pre.withReturnData [])
              gas
              value caller target codeAddress stv istat
              ((pre.memory.read ii is).1) code delegated)) raw = true
       then Exec.flowActions dp ca child else []) := by
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · rcases run with ⟨hxl, -⟩
    cases hxl
  · rcases run with ⟨hxl, -⟩
    cases hxl
  · obtain ⟨result, hframe, hresume⟩ := run
    cases result with
    | error error =>
        simp [Resume.run, liftToExecution] at hresume
    | ok settled =>
        have henter := (RunFrame.some_inv hframe).1
        rcases Frame.enter_run_inv henter with
          ⟨benv, htransfer, hinit⟩
        have hsumChild : sum cevm.dyna.state.bal < 2 ^ 256 := by
          have hnoninc := Msg.benvAfterTransfer_balance_effect htransfer
          have hpreEq :=
            congrArg (fun e : Evm => e.dyna.state.bal) hinit
          dsimp [initEvm, initDevm, Msg.withBenv] at hpreEq
          rw [hpreEq]
          exact lt_of_le_of_lt hnoninc hsum
        have hcallerMsg :
            (callMsg sevm (pre.withReturnData [])
              gas
              value caller target codeAddress stv istat
              ((pre.memory.read ii is).1) code delegated
            ).shouldTransferValue = true →
              (callMsg sevm (pre.withReturnData [])
                gas
                value caller target codeAddress stv istat
                ((pre.memory.read ii is).1) code delegated
              ).caller ≠ ca := by
          simpa [callMsg] using hcaller
        have hval0Msg :
            (callMsg sevm (pre.withReturnData [])
              gas
              value caller target codeAddress stv istat
              ((pre.memory.read ii is).1) code delegated
            ).shouldTransferValue = false →
              (callMsg sevm (pre.withReturnData [])
                gas
                value caller target codeAddress stv istat
                ((pre.memory.read ii is).1) code delegated
              ).currentTarget = ca →
              (callMsg sevm (pre.withReturnData [])
                gas
                value caller target codeAddress stv istat
                ((pre.memory.read ii is).1) code delegated
              ).value = 0 := by
          simpa [callMsg] using hval0
        have hbody : ∀
            (hcommit : Execution.commits raw = true),
            EthBound ca cevm.dyna.state
              (Execution.committedPost raw hcommit).state
              (Exec.bodyEthActions dp ca child hcommit) := by
          intro hcommit
          have hpc := congrArg Evm.pc hinit
          have hmem := congrArg (fun e : Evm => e.dyna.memory) hinit
          dsimp [initEvm, initDevm, Msg.withBenv] at hpc hmem
          have hroot : Exec.Frame.IsRoot
              (Exec.Frame.ofRun child hcommit) := ⟨hpc, hmem⟩
          exact childSound child hcommit hchildAt
            (fun htarget => ⟨hroot, hdirect htarget⟩) hsumChild
        have hbound :=
          ProcessMessage.ethBound_of_settledBodyBound
            child hframe hcallerMsg hval0Msg
            (by
              change sum pre.state.bal < 2 ^ 256
              exact hsum) hbody
        have hresumeBal : post.state.bal = settled.state.bal :=
          congrArg State.bal (Resume.call_state hresume.symm)
        unfold EthBound at hbound ⊢
        rw [hresumeBal]
        exact hbound

/-- Recursive CREATE transport for a foreign parent, including constructor
entry and complete code-deposit settlement. -/
theorem GenericCreate.foreignSomeEthBound
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {cevm : Evm} {raw : Execution} {post : Devm}
    (run : GenericCreate sevm pre endowment newAddress mi ms
      (.some ⟨cevm, raw⟩) (.ok post))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (childSound : Exec.CoreEthSound dp ca
      cevm.pc cevm.sta cevm.dyna raw)
    (hchildAt : Prog.At (weth10 dp) ca
      cevm.pc cevm.sta cevm.dyna)
    (hdirect : cevm.sta.currentTarget = ca →
      cevm.sta.codeAddress = some ca)
    (hforeign : sevm.currentTarget ≠ ca)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state
      (if Blanc.Weth10.Frame.settlementCommits
          (Frame.ofCreate
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1))) raw = true
       then Exec.flowActions dp ca child else []) := by
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  all_goals try
    (have hxl : (some ⟨cevm, raw⟩ : Xlot) = none := run.1
     cases hxl)
  obtain ⟨result, hframe, hresume⟩ := run
  cases result with
  | error error =>
      simp [Resume.run, liftToExecution] at hresume
  | ok settled =>
      have henter := (RunFrame.some_inv hframe).1
      rcases Frame.enter_run_inv henter with
        ⟨benv, htransfer, hinit⟩
      have hstartBal :
          (createMsg sevm
            (addAccessedAddress
              (((pre.withGasLeft
                  (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                []).incrNonce sevm.currentTarget) newAddress)
            (except64th pre.gasLeft) endowment newAddress
            (Array.sliceD pre.memory.data mi ms 0)).benv.state.bal =
              pre.state.bal :=
        genericCreate_prepared_bal sevm pre newAddress
      have hsumParent :
          sum (createMsg sevm
            (addAccessedAddress
              (((pre.withGasLeft
                  (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                []).incrNonce sevm.currentTarget) newAddress)
            (except64th pre.gasLeft) endowment newAddress
            ((pre.memory.read mi ms).1)).benv.state.bal < 2 ^ 256 := by
        change sum (addAccessedAddress
          (((pre.withGasLeft
              (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress).state.bal <
              2 ^ 256
        rw [genericCreate_prepared_bal]
        exact hsum
      have hsumInner :
          sum (Frame.ofCreate
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1))).inner.benv.state.bal <
            2 ^ 256 := by
        change sum (processCreateMessage.msg
          (createMsg sevm
            (addAccessedAddress
              (((pre.withGasLeft
                  (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                []).incrNonce sevm.currentTarget) newAddress)
            (except64th pre.gasLeft) endowment newAddress
            ((pre.memory.read mi ms).1))).benv.state.bal < 2 ^ 256
        rw [processCreateMessage_msg_bal_eq]
        exact hsumParent
      have hsumChild : sum cevm.dyna.state.bal < 2 ^ 256 := by
        have hnoninc := Msg.benvAfterTransfer_balance_effect htransfer
        have hpreEq :=
          congrArg (fun e : Evm => e.dyna.state.bal) hinit
        dsimp [initEvm, initDevm, Msg.withBenv] at hpreEq
        rw [hpreEq]
        exact lt_of_le_of_lt hnoninc hsumInner
      have hcallerMsg :
          (createMsg sevm
            (addAccessedAddress
              (((pre.withGasLeft
                  (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                []).incrNonce sevm.currentTarget) newAddress)
            (except64th pre.gasLeft) endowment newAddress
            ((pre.memory.read mi ms).1)).shouldTransferValue = true →
          (createMsg sevm
            (addAccessedAddress
              (((pre.withGasLeft
                  (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                []).incrNonce sevm.currentTarget) newAddress)
            (except64th pre.gasLeft) endowment newAddress
            ((pre.memory.read mi ms).1)).caller ≠ ca := by
        simpa [createMsg] using hforeign
      have hbody : ∀
          (hcommit : Execution.commits raw = true),
          EthBound ca cevm.dyna.state
            (Execution.committedPost raw hcommit).state
            (Exec.bodyEthActions dp ca child hcommit) := by
        intro hcommit
        have hpc := congrArg Evm.pc hinit
        have hmem := congrArg (fun e : Evm => e.dyna.memory) hinit
        dsimp [initEvm, initDevm, Msg.withBenv] at hpc hmem
        have hroot : Exec.Frame.IsRoot
            (Exec.Frame.ofRun child hcommit) := ⟨hpc, hmem⟩
        exact childSound child hcommit hchildAt
          (fun htarget => ⟨hroot, hdirect htarget⟩) hsumChild
      have hbound :=
        ProcessCreateMessage.ethBound_of_settledBodyBound
          child hframe hcallerMsg (by simp [createMsg])
          hsumParent hbody
      have hresumeBal : post.state.bal = settled.state.bal :=
        congrArg State.bal (Resume.create_state hresume.symm)
      unfold EthBound at hbound ⊢
      rw [hresumeBal]
      rw [hstartBal] at hbound
      exact hbound

/-- A CALL-family instruction which finishes without an interpreter child
cannot decrease `ca` when the executing account is foreign.  Early exits are
balance-silent; an empty-code or precompile child is accounted through its
actual `ProcessMessage` entry and settled world. -/
theorem GenericCall.foreignNoneEthBound
    {ca : Adr} {sevm : Sevm} {pre : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv istat : Bool}
    {ii is oi os : Nat} {code : ByteArray} {delegated : Bool}
    {post : Devm}
    (run : GenericCall sevm pre gas value caller target codeAddress
      stv istat ii is oi os code delegated .none (.ok post))
    (hcaller : stv = true → caller ≠ ca)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state [] := by
  unfold GenericCall genericCall.step at run
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.2
  · rename_i heq
    have hpost := Except.ok.inj run.2
    subst post
    have hpush := Devm.push_instructionFrame 0
      ((pre.withReturnData []).withGasLeft
        ((pre.withReturnData []).gasLeft + gas))
    rw [heq] at hpush
    exact (EthStep.silent (ca := ca)
      (congrArg (fun s : State => s.bal ca)
        hpush.state.symm)).bound
  · obtain ⟨result, hframe, hresume⟩ := run
    cases result with
    | error error =>
        simp [Resume.run, liftToExecution] at hresume
    | ok child =>
        have hcallerNe :
            (callMsg sevm (pre.withReturnData [])
              gas
              value caller target codeAddress stv istat
              ((pre.memory.read ii is).1) code delegated
            ).shouldTransferValue = true →
              (callMsg sevm (pre.withReturnData [])
                gas
                value caller target codeAddress stv istat
                ((pre.memory.read ii is).1) code delegated
              ).caller ≠ ca := by
          simpa [callMsg] using hcaller
        have hbound := ProcessMessage.ethBound_of_none_conditions
          hframe hcallerNe (by
            change sum pre.state.bal < 2 ^ 256
            exact hsum)
        have hresumeBal : post.state.bal = child.state.bal :=
          congrArg State.bal (Resume.call_state hresume.symm)
        unfold EthBound at hbound ⊢
        simp only [flowActionsEthMint, List.map_nil, List.sum_nil,
          flowActionsEthRedemption, Nat.add_zero] at hbound ⊢
        rw [hresumeBal]
        exact hbound

/-- CREATE-family no-slot execution has the same foreign-source property.
Nonce/access preparation and code-deposit settlement are balance-silent; the
actual endowment entry is handled by the no-slot CREATE theorem. -/
theorem GenericCreate.foreignNoneEthBound
    {ca : Adr} {sevm : Sevm} {pre : Devm}
    {endowment : B256} {newAddress : Adr} {mi ms : Nat}
    {post : Devm}
    (run : GenericCreate sevm pre endowment newAddress mi ms
      .none (.ok post))
    (hforeign : sevm.currentTarget ≠ ca)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state [] := by
  unfold GenericCreate genericCreate.step at run
  simp only [Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at run
  repeat' split at run
  all_goals simp only [XStep.ofExcept, XStep.Run] at run
  · cases run.2
  · cases run.2
  · cases run.2
  · rename_i heq
    have hpost := Except.ok.inj run.2
    subst post
    have hpush := Devm.push_instructionFrame 0
      (((pre.withGasLeft
          (pre.gasLeft - except64th pre.gasLeft)).withReturnData
        []).withGasLeft
          (((pre.withGasLeft
              (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).gasLeft + except64th pre.gasLeft))
    rw [heq] at hpush
    exact (EthStep.silent (ca := ca)
      (congrArg (fun s : State => s.bal ca)
        hpush.state.symm)).bound
  · cases run.2
  · rename_i heq
    have hpost := Except.ok.inj run.2
    subst post
    have hpush := Devm.push_instructionFrame 0
      (addAccessedAddress
        (((pre.withGasLeft
          (pre.gasLeft - except64th pre.gasLeft)).withReturnData
            []).incrNonce sevm.currentTarget) newAddress)
    rw [heq] at hpush
    have hbal := genericCreate_prepared_bal sevm pre newAddress
    exact (EthStep.silent (ca := ca)
      ((congrArg (fun s : State => s.bal ca)
        hpush.state.symm).trans (congrFun hbal ca))).bound
  · obtain ⟨result, hframe, hresume⟩ := run
    cases result with
    | error error =>
        simp [Resume.run, liftToExecution] at hresume
    | ok child =>
        have hcallerNe :
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1)).shouldTransferValue = true →
            (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1)).caller ≠ ca := by
          intro _
          simpa [createMsg] using hforeign
        have hsumParent :
            sum (createMsg sevm
              (addAccessedAddress
                (((pre.withGasLeft
                    (pre.gasLeft - except64th pre.gasLeft)).withReturnData
                  []).incrNonce sevm.currentTarget) newAddress)
              (except64th pre.gasLeft) endowment newAddress
              ((pre.memory.read mi ms).1)).benv.state.bal < 2 ^ 256 := by
          change sum (addAccessedAddress
            (((pre.withGasLeft
                (pre.gasLeft - except64th pre.gasLeft)).withReturnData
              []).incrNonce sevm.currentTarget) newAddress).state.bal <
                2 ^ 256
          rw [genericCreate_prepared_bal]
          exact hsum
        have hbound := ProcessCreateMessage.ethBound_of_none_conditions
          hframe hcallerNe hsumParent
        have hresumeBal : post.state.bal = child.state.bal :=
          congrArg State.bal (Resume.create_state hresume.symm)
        unfold EthBound at hbound ⊢
        simp only [flowActionsEthMint, List.map_nil, List.sum_nil,
          flowActionsEthRedemption, Nat.add_zero] at hbound ⊢
        rw [hresumeBal]
        change
          ((addAccessedAddress
            (((pre.withGasLeft
                (pre.gasLeft - except64th pre.gasLeft)).withReturnData
              []).incrNonce sevm.currentTarget) newAddress).state.bal ca).toNat ≤
            (child.state.bal ca).toNat at hbound
        rw [genericCreate_prepared_bal] at hbound
        exact hbound

/-- Contract-neutral no-child bound for any call-type opcode. -/
theorem Xinst.foreignNoneEthBound
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {x : Xinst}
    (run : Xinst.Run sevm pre x .none (.ok post))
    (hforeign : sevm.currentTarget ≠ ca)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state [] := by
  unfold Xinst.Run at run
  rcases Xinst.step_shape sevm pre x with
    ⟨ex, hs, hframe⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isSt,
      ii, isz, oi, osz, code, delegated, hprefix, _, hcal, _, hs⟩ <;>
    rw [hs] at run
  · obtain ⟨-, rfl⟩ := run
    exact (EthStep.silent (ca := ca)
      (congrArg (fun s : State => s.bal ca)
        hframe.state.symm)).bound
  · have hsumD : sum d.state.bal < 2 ^ 256 := by
      rw [← hprefix.state]
      exact hsum
    have hbound := GenericCreate.foreignNoneEthBound
      run hforeign hsumD
    unfold EthBound at hbound ⊢
    rw [hprefix.state]
    exact hbound
  · have hsumD : sum d.state.bal < 2 ^ 256 := by
      rw [← hprefix.state]
      exact hsum
    have hcaller : stv = true → caller ≠ ca := by
      intro hstv
      rcases hcal with ⟨_, hcaller⟩ | ⟨hfalse, _⟩
      · rw [hcaller]
        exact hforeign
      · rw [hstv] at hfalse
        contradiction
    have hbound := GenericCall.foreignNoneEthBound
      run hcaller hsumD
    unfold EthBound at hbound ⊢
    rw [hprefix.state]
    exact hbound

/-- Contract-neutral recursive transport for an actual filled `Xinst` slot.
The shape theorem removes the instruction prefix, and the exact-spawn lemmas
identify the settlement predicate with the frame retained by `Exec`. -/
theorem Xinst.foreignSomeEthBound
    {dp : DeployParams} {ca : Adr}
    {sevm : Sevm} {pre : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled post : Devm}
    (hspawn : Xinst.step sevm pre x = .spawn frame resume)
    (hframe : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (hresume : resume.run (.ok settled) = .ok post)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (childSound : Exec.CoreEthSound dp ca
      cevm.pc cevm.sta cevm.dyna raw)
    (hchildAt : Prog.At (weth10 dp) ca
      cevm.pc cevm.sta cevm.dyna)
    (hdirect : cevm.sta.currentTarget = ca →
      cevm.sta.codeAddress = some ca)
    (hforeign : sevm.currentTarget ≠ ca)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state
      (if Blanc.Weth10.Frame.settlementCommits frame raw = true
       then Exec.flowActions dp ca child else []) := by
  rcases Xinst.step_shape sevm pre x with
    ⟨ex, hs, hprefix⟩ |
    ⟨d, endowment, newAddress, mi, ms, hprefix, hs⟩ |
    ⟨d, d₀, gas, value, caller, target, codeAddress, stv, isSt,
      ii, isz, oi, osz, code, delegated, hprefix, _, hcal, _, hs⟩ <;>
    rw [hs] at hspawn
  · cases hspawn
  · rcases genericCreate_step_spawn_exact hspawn with ⟨rfl, rfl⟩
    have grun : GenericCreate sevm d endowment newAddress mi ms
        (.some ⟨cevm, raw⟩) (.ok post) := by
      unfold GenericCreate XStep.Run
      rw [hspawn]
      exact ⟨.ok settled, hframe, hresume.symm⟩
    have hbound := GenericCreate.foreignSomeEthBound
      grun child childSound hchildAt hdirect hforeign
      (by rw [← hprefix.state]; exact hsum)
    unfold EthBound at hbound ⊢
    rw [hprefix.state]
    exact hbound
  · rcases genericCall_step_spawn_exact hspawn with ⟨rfl, rfl⟩
    have grun : GenericCall sevm d gas value caller target codeAddress
        stv isSt ii isz oi osz code delegated
        (.some ⟨cevm, raw⟩) (.ok post) := by
      unfold GenericCall XStep.Run
      rw [hspawn]
      exact ⟨.ok settled, hframe, hresume.symm⟩
    have hcaller : stv = true → caller ≠ ca := by
      intro hstv
      rcases hcal with ⟨_, hcaller⟩ | ⟨hfalse, _⟩
      · rw [hcaller]
        exact hforeign
      · rw [hstv] at hfalse
        contradiction
    have hval0 : stv = false → target = ca → value = 0 := by
      intro hstv htarget
      rcases hcal with ⟨htrue, _⟩ | ⟨_, htargetParent⟩
      · rw [hstv] at htrue
        contradiction
      · exact False.elim
          (hforeign (htargetParent.symm.trans htarget))
    have hbound := GenericCall.foreignSomeEthBound
      grun child childSound hchildAt hdirect hcaller hval0
      (by rw [← hprefix.state]; exact hsum)
    unfold EthBound at hbound ⊢
    rw [hprefix.state]
    exact hbound

/-- Any nonterminal opcode which uses no recursive slot is ETH-silent or an
unclassified non-wrapping inward transfer when the current frame is foreign. -/
theorem Ninst.foreignNoneEthBound
    {ca : Adr} {pc : Nat} {sevm : Sevm} {pre post : Devm} {n : Ninst}
    (run : Ninst.StepRun pc sevm pre n .none (.ok post))
    (hforeign : sevm.currentTarget ≠ ca)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state [] := by
  cases n with
  | reg r =>
      simp only [Ninst.StepRun, Ninst.step_reg,
        Step.run_ofExecution] at run
      have hrun : Rinst.run ⟨pc, sevm, pre⟩ r = .ok post :=
        run.2.symm
      have hbal := Rinst.preserves_bal hrun
      exact (EthStep.silent (ca := ca) (congrFun hbal.symm ca)).bound
  | exec x =>
      simp only [Ninst.StepRun, Ninst.step_exec] at run
      exact Xinst.foreignNoneEthBound
        (XStep.run_toStep.mp run) hforeign hsum
  | push xs hxs =>
      have hrel := Ninst.push_instructionFrame_effectRec
        (hxs := hxs) (xl := .none) trivial run
      have hframe : Devm.InstructionFrame pre post := by
        simpa [Execution.Rel, Outcome.Rel] using hrel
      exact (EthStep.silent (ca := ca)
        (congrArg (fun s : State => s.bal ca)
          hframe.state.symm)).bound

/-- `SELFDESTRUCT` executed by a foreign account can only leave `ca`
unchanged or credit it from the foreign source.  The latter is recorded as an
unclassified inward transfer; the global balance bound rules out wrapping. -/
theorem Linst.foreignDestEthBound
    {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Linst.Run sevm pre .dest (.ok post))
    (hforeign : sevm.currentTarget ≠ ca)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state [] := by
  dsimp [Linst.Run, Linst.run] at run
  rcases Except.bind_eq_ok run with
    ⟨⟨dest, devm1⟩, hpop, hrun1⟩
  rcases Except.bind_eq_ok hrun1 with
    ⟨devm2, hcharge, hrun2⟩
  rcases Except.bind_eq_ok hrun2 with
    ⟨_, hassert, hrun3⟩
  rcases Except.bind_eq_ok hrun3 with
    ⟨devm3, hsub, hrun4⟩
  have hsubSome : devm2.subBal sevm.currentTarget
      (devm1.getAcct sevm.currentTarget).bal = some devm3 := by
    cases heq : devm2.subBal sevm.currentTarget
        (devm1.getAcct sevm.currentTarget).bal
    · rw [heq] at hsub
      contradiction
    · rw [heq] at hsub
      injection hsub with h
      subst h
      rfl
  have hsubState : devm2.state.subBal sevm.currentTarget
      (devm1.getAcct sevm.currentTarget).bal = some devm3.state := by
    dsimp [Devm.subBal, Option.bind] at hsubSome
    cases heq : devm2.state.subBal sevm.currentTarget
        (devm1.getAcct sevm.currentTarget).bal
    · rw [heq] at hsubSome
      contradiction
    · rw [heq] at hsubSome
      injection hsubSome with h
      subst h
      rfl
  have hbal2 : devm2.state.bal = pre.state.bal := by
    have hchargeBal : devm2.getBal =
        (if dest ∉ devm1.accessedAddresses then
          addAccessedAddress devm1 dest else devm1).getBal := by
      funext a
      by_cases hcold : dest ∉ devm1.accessedAddresses
      · rw [if_pos hcold]
        simpa [hcold] using chargeGas_getBal_eq hcharge a
      · rw [if_neg hcold]
        simpa [hcold] using chargeGas_getBal_eq hcharge a
    have hpopBal : devm1.getBal = pre.getBal := by
      funext a
      exact Devm.popToAdr_getBal_eq hpop a
    change devm2.getBal = pre.getBal
    exact hchargeBal.trans (by split <;> exact hpopBal)
  have hsum2 : sum devm2.state.bal < 2 ^ 256 := by
    rw [hbal2]
    exact hsum
  let transferred := devm3.addBal dest
    (devm1.getAcct sevm.currentTarget).bal
  have hmove : EthBound ca devm2.state transferred.state [] := by
    by_cases hdest : dest = ca
    · subst dest
      exact (EthStep.unclassifiedInward hforeign hsubState rfl hsum2).bound
    · exact (EthStep.unrelatedTransfer hforeign hdest
        hsubState rfl).bound
  have hpostBal : post.state.bal ca = transferred.state.bal ca := by
    dsimp only at hrun4
    split at hrun4
    · have heq := Except.ok.inj hrun4
      rw [← heq]
      change ((transferred.setBal sevm.currentTarget 0).state.bal ca) =
        transferred.state.bal ca
      show ((transferred.state.setBal sevm.currentTarget 0).get ca).bal =
        (transferred.state.get ca).bal
      rw [State.setBal_get_ne hforeign]
    · have heq := Except.ok.inj hrun4
      rw [← heq]
  unfold EthBound at hmove ⊢
  rw [← hbal2, hpostBal]
  exact hmove

/-- Every terminal opcode run by a foreign frame is ETH-sound.  Return is
balance-silent, revert cannot commit, and selfdestruct is handled above. -/
theorem Linst.foreignEthBound
    {ca : Adr} {sevm : Sevm} {pre post : Devm} {l : Linst}
    (run : Linst.Run sevm pre l (.ok post))
    (hforeign : sevm.currentTarget ≠ ca)
    (hsum : sum pre.state.bal < 2 ^ 256) :
    EthBound ca pre.state post.state [] := by
  cases l with
  | stop =>
      simp [Linst.Run, Linst.run] at run
      subst post
      exact EthBound.refl ca pre.state
  | ret =>
      have hframe := Linst.run_instructionFrame sevm pre .ret (by decide)
      rw [run] at hframe
      exact (EthStep.silent (ca := ca)
        (congrArg (fun s : State => s.bal ca)
          hframe.state.symm)).bound
  | rev =>
      unfold Linst.Run Linst.run at run
      rcases hpop1 : pre.popToNat with error | ⟨index, devm1⟩
      · simp [hpop1, bind, Except.bind] at run
      · simp only [hpop1, bind, Except.bind] at run
        rcases hpop2 : devm1.popToNat with error | ⟨size, devm2⟩
        · simp [hpop2] at run
        · simp only [hpop2] at run
          rcases hcharge : chargeGas
              (devm2.extCost [(index, size)]) devm2 with error | devm3
          · simp [hcharge] at run
          · simp [hcharge] at run
  | dest =>
      exact Linst.foreignDestEthBound run hforeign hsum

/-- Away from `ca`, the body list has no root action and is exactly the
proper-descendant traversal. -/
theorem Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (hcommit : Execution.commits out = true)
    (hne : sevm.currentTarget ≠ ca) :
    Exec.bodyEthActions dp ca run hcommit =
      Exec.descendantActions dp ca run := by
  have hnot : ¬ (Exec.Frame.ofRun run hcommit).exactInvocation dp ca := by
    rintro ⟨_, htarget, _, _⟩
    exact hne htarget
  simp [Exec.bodyEthActions, Exec.descendantActions,
    Exec.Frame.flowAction?, flowActionBodyEthActions, hnot]

/-- Contract-specific operational accounting indexed by the authentic frame's
actual root classification and rollback-pruned descendant ledger. -/
inductive Exec.Frame.CompiledBodyEthAccounting
    (dp : DeployParams) (ca : Adr) (frame : Exec.Frame) : Prop
  | flow (action : FlowAction)
      (classified : frame.flowAction? dp ca = some action)
      (accounting : RichBodyEthAccounting dp ca frame.sevm
        frame.pre frame.post action (frame.descendantFlowActions dp ca))
  | noFlow
      (classified : frame.flowAction? dp ca = none)
      (accounting : NoFlowBodyEthAccounting dp ca frame.sevm
        frame.pre frame.post (frame.descendantFlowActions dp ca))

/-- Reusable ETH closure for a recognized nonpayable body whose source line
contains no recursive machine instruction and ends at one terminal opcode. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {line : Line} {i : Linst}
    (context : frame.AuthenticContext dp ca)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (classified : frame.flowAction? dp ca = none)
    (hmem : (Sevm.selector frame.sevm,
      nonpayable (line +++ Func.last i)) ∈ weth10Funcs dp)
    (hchildless : ∀ n ∈ line, NinstIsChildless n)
    (balance : Devm.getBal frame.post = Devm.getBal frame.pre) :
    frame.CompiledBodyEthAccounting dp ca := by
  apply Exec.Frame.CompiledBodyEthAccounting.noFlow classified
  exact NoFlowBodyEthAccounting.silent balance
    (frame.descendantFlowActions_eq_nil_of_nonpayableChildless
      context hnonempty hmem hchildless)

/-- ETH-local chronology closure for a nonpayable body made of a childless
guard prefix and two childless terminal branches. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildlessBranches_noFlow
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {head left right : Line} {leftLast rightLast : Linst}
    (context : frame.AuthenticContext dp ca)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (classified : frame.flowAction? dp ca = none)
    (hmem : (Sevm.selector frame.sevm,
      nonpayable (head +++
        ((left +++ Func.last leftLast) <?>
          (right +++ Func.last rightLast)))) ∈ weth10Funcs dp)
    (hhead : ∀ n ∈ head, NinstIsChildless n)
    (hleft : ∀ n ∈ left, NinstIsChildless n)
    (hright : ∀ n ∈ right, NinstIsChildless n)
    (balance : Devm.getBal frame.post = Devm.getBal frame.pre) :
    frame.CompiledBodyEthAccounting dp ca := by
  apply Exec.Frame.CompiledBodyEthAccounting.noFlow classified
  apply NoFlowBodyEthAccounting.silent balance
  rcases frame.compiledSelectorBodyCursor context hnonempty hmem with
    ⟨wrapperCursor, _hwrapperStack, hwrapperActions⟩
  rcases wrapperCursor.enterNonpayable with
    ⟨bodyCursor, _hbodyStack, hbodyActions⟩
  rcases bodyCursor.peelChildlessLine hhead with
    ⟨branchCursor, _hheadRun, hheadActions⟩
  rcases branchCursor.selectBranchWithActions with hactual | hactual
  · rcases hactual with ⟨leftCursor, hleftActions⟩
    exact (leftCursor.finishChildlessLine hright).trans
      (hleftActions.trans
        (hheadActions.trans (hbodyActions.trans hwrapperActions)))
  · rcases hactual with ⟨rightCursor, hrightActions⟩
    exact (rightCursor.finishChildlessLine hleft).trans
      (hrightActions.trans
        (hheadActions.trans (hbodyActions.trans hwrapperActions)))

/-- Exact no-flow ETH accounting for `name()`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_name
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm = selector "name" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := name_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        [Ninst.pushB256 (Blanc.String.toBytes "Wrapped Ether v10").toB256,
          Ninst.pushB256 120, Ninst.shl] ++
        pushList [17, 32] ++
        mstoreAt 0 ++ mstoreAt 1 ++ mstoreAt 2 ++
        pushList [96, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "name" [], nonpayable name) ∈ weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, pushList, mstoreAt, NinstIsChildless,
          Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `symbol()`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_symbol
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm = selector "symbol" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := symbol_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        [Ninst.pushB256 (Blanc.String.toBytes "WETH10").toB256,
          Ninst.pushB256 208, Ninst.shl] ++
        pushList [6, 32] ++
        mstoreAt 0 ++ mstoreAt 1 ++ mstoreAt 2 ++
        pushList [96, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "symbol" [], nonpayable symbol) ∈ weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, pushList, mstoreAt, NinstIsChildless,
          Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `CALLBACK_SUCCESS()`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_callbackSuccess
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector :
      Sevm.selector frame.sevm = selector "CALLBACK_SUCCESS" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := callbackSuccess_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        [Ninst.pushB256 CALLBACK_SUCCESS] ++
        mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "CALLBACK_SUCCESS" [], nonpayable callbackSuccess) ∈
          weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, pushList, mstoreAt, NinstIsChildless,
          Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `PERMIT_TYPEHASH()`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_permitTypehash
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector :
      Sevm.selector frame.sevm = selector "PERMIT_TYPEHASH" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := permitTypehash_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        [Ninst.pushB256 PERMIT_TYPEHASH] ++
        mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "PERMIT_TYPEHASH" [], nonpayable permitTypehash) ∈
          weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, pushList, mstoreAt, NinstIsChildless,
          Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `decimals()`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_decimals
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm = selector "decimals" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := decimals_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        [Ninst.pushB256 0x12] ++ mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "decimals" [], nonpayable decimals) ∈ weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, pushList, mstoreAt,
          NinstIsChildless, Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `deploymentChainId()`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_deploymentChainId
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector :
      Sevm.selector frame.sevm = selector "deploymentChainId" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := deploymentChainId_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        [pushDeployWord dp.deploymentChainId] ++
        mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "deploymentChainId" [],
          nonpayable (deploymentChainId dp)) ∈ weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, pushDeployWord, pushList, mstoreAt,
          NinstIsChildless, Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `DOMAIN_SEPARATOR()`, including both
childless chain-id branches. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_domainSeparator
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector :
      Sevm.selector frame.sevm = selector "DOMAIN_SEPARATOR" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := domainSeparator_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let head : Line :=
        [Ninst.chainid, Ninst.dup 0,
          pushDeployWord dp.deploymentChainId, Ninst.eq]
      let left : Line :=
        [Ninst.pop, pushDeployWord dp.cachedDomainSeparator] ++
        mstoreAt 0 ++ pushList [32, 0]
      let right : Line :=
        calculateDomainSeparator ++ mstoreAt 0 ++ pushList [32, 0]
      apply
        Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildlessBranches_noFlow
          (head := head) (left := left) (right := right)
          (leftLast := .ret) (rightLast := .ret)
          context hnonempty classified
      · rw [hselector]
        change (selector "DOMAIN_SEPARATOR" [],
          nonpayable (domainSeparator dp)) ∈ weth10Funcs dp
        simp [weth10Funcs]
      · simp [head, pushDeployWord, NinstIsChildless]
      · simp [left, pushDeployWord, pushList, mstoreAt,
          NinstIsChildless, Ninst.pushB256]
      · simp [right, calculateDomainSeparator, pushList, mstoreAt,
          NinstIsChildless, Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `maxFlashLoan(address)`, including both
childless token-test branches. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_maxFlashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm =
      selector "maxFlashLoan" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := maxFlashLoan_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let head : Line := arg 0 ++ [Ninst.address, Ninst.eq]
      let left : Line :=
        pushFlashMintedSlot ++
        [Ninst.sload, Ninst.pushB256 (Nat.toB256 maxFlashMinted), Ninst.sub] ++
        mstoreAt 0 ++ pushList [32, 0]
      let right : Line :=
        [Ninst.pushB256 0] ++ mstoreAt 0 ++ pushList [32, 0]
      apply
        Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildlessBranches_noFlow
          (head := head) (left := left) (right := right)
          (leftLast := .ret) (rightLast := .ret)
          context hnonempty classified
      · rw [hselector]
        change (selector "maxFlashLoan" [.address],
          nonpayable maxFlashLoan) ∈ weth10Funcs dp
        simp [weth10Funcs]
      · simp [head, arg, cdl, NinstIsChildless, Ninst.pushB256]
      · simp [left, pushFlashMintedSlot, pushList, mstoreAt,
          NinstIsChildless, Ninst.pushB256]
      · simp [right, pushList, mstoreAt, NinstIsChildless,
          Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for successful `flashFee(address,uint256)`.
The reverting token-mismatch arm cannot be the committed frame; the retained
successful arm is balance-silent and its original descendant chronology is
empty. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_flashFee
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm =
      selector "flashFee" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := flashFee_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      apply Exec.Frame.CompiledBodyEthAccounting.noFlow classified
      exact NoFlowBodyEthAccounting.silent heffect.2.2.2.1
        (Exec.Frame.descendantFlowActions_eq_nil_of_flashFee
          context hselector hnonempty)

/-- Exact no-flow ETH accounting for `balanceOf(address)`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_balanceOf
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector :
      Sevm.selector frame.sevm = selector "balanceOf" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := balanceOf_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        arg 0 ++ [Ninst.sload] ++ mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "balanceOf" [.address],
          nonpayable balanceOfEndpoint) ∈ weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, arg, cdl,
          pushList, mstoreAt, NinstIsChildless, Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `allowance(address,address)`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_allowance
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm =
      selector "allowance" [.address, .address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := allowance_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        argCopy 0 0 2 ++ allowanceKeyFromMemory ++ [Ninst.sload] ++
        mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "allowance" [.address, .address],
          nonpayable allowance) ∈ weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, argCopy, cdc, allowanceKeyFromMemory,
          pushList, mstoreAt, NinstIsChildless, Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `nonces(address)`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_nonces
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector :
      Sevm.selector frame.sevm = selector "nonces" [.address])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := nonces_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        arg 0 ++ tagNonceKey ++ [Ninst.sload] ++
        mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "nonces" [.address], nonpayable nonces) ∈
          weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, arg, cdl, tagNonceKey, pushList, mstoreAt,
          NinstIsChildless, Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `flashMinted()`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_flashMinted
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm = selector "flashMinted" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := flashMinted_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        pushFlashMintedSlot ++ [Ninst.sload] ++
        mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "flashMinted" [], nonpayable flashMinted) ∈
          weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, pushFlashMintedSlot, pushList,
          mstoreAt, NinstIsChildless, Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for `totalSupply()`.  The body reads
`SELFBALANCE`, but does not alter the contract balance. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_totalSupply
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm = selector "totalSupply" [])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have heffect := totalSupply_exec_output context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      let line : Line :=
        [Ninst.selfbalance] ++ pushFlashMintedSlot ++
        [Ninst.sload, Ninst.add] ++ mstoreAt 0 ++ pushList [32, 0]
      apply Exec.Frame.compiledBodyEthAccounting_of_nonpayableChildless_noFlow
        (line := line) (i := .ret) context hnonempty classified
      · rw [hselector]
        change (selector "totalSupply" [], nonpayable totalSupply) ∈
          weth10Funcs dp
        simp [weth10Funcs]
      · simp [line, pushFlashMintedSlot, pushList,
          mstoreAt, NinstIsChildless, Ninst.pushB256]
      · exact heffect.2.2.2.1

/-- Exact no-flow ETH accounting for the call-free `approve` body. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_approve
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = none)
    (hselector : Sevm.selector frame.sevm =
      selector "approve" [.address, .uint256])
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      apply Exec.Frame.CompiledBodyEthAccounting.noFlow classified
      have heffect := approve_exec_effect dp context.memory_wf
        context.memory_reads_empty run context.invocation.2.2.2
        hselector hnonempty
      exact NoFlowBodyEthAccounting.silent heffect.2.2.2.2.1
        (Exec.Frame.descendantFlowActions_eq_nil_of_approve
          context hselector hnonempty)

/-- Exact ETH accounting for the successful nonzero-recipient `transfer`
branch.  Its root action has zero ETH weight and the body is balance-silent
with no retained child. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_transferNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = some action)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      apply Exec.Frame.CompiledBodyEthAccounting.flow action classified
      have hatom : primaryFlowAtom e = some
          (.transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
            (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          transferSelector_ne_depositSelector,
          transferSelector_ne_depositToSelector,
          transferSelector_ne_depositToAndCallSelector, hto]
      have hactionAtom : action.atom =
          .transfer e.caller.toB256 (Sevm.argWord e 0) e.caller
            (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toNat := by
        unfold Exec.Frame.flowAction? at classified
        rw [if_pos context.invocation, hatom] at classified
        exact congrArg FlowAction.atom
          (Option.some.inj classified).symm
      have heffect := (weth10_transfer_successEffect dp
        context.memory_wf context.memory_reads_empty run
        context.invocation.2.2.2
        (by simpa only [transferSelector] using hselector)
        hnonempty).2
      rcases heffect with hzero | hnonzero
      · exact (hto hzero.1).elim
      · rcases hnonzero with
          ⟨_, _, _, _, _, _, _, hbalance, _⟩
        exact RichBodyEthAccounting.zeroSilent
          (by simp [FlowAction.bodyEthActions, hactionAtom])
          (by simp [FlowAtom.ethMint, hactionAtom])
          (by simp [FlowAtom.ethRedemption, hactionAtom])
          hbalance
          (Exec.Frame.descendantFlowActions_eq_nil_of_transferNonzero
            context hselector hnonempty hto)

/-- ETH accounting for the delegated nonzero-recipient transfer core.  The
allowance prefix and transfer body preserve ETH balances; only its exact
call-free cursor chronology remains an input. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_transferFromNonzero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 1 ≠ 0)
    (chronology : frame.descendantFlowActions dp ca = []) :
    frame.CompiledBodyEthAccounting dp ca := by
  cases haction : frame.flowAction? dp ca with
  | none =>
      have hprimary : primaryFlowAtom frame.sevm = some
          (.transfer (Sevm.argWord frame.sevm 0)
            (Sevm.argWord frame.sevm 1)
            (Sevm.argWord frame.sevm 0).toAdr
            (Sevm.argWord frame.sevm 1).toAdr
            (Sevm.argWord frame.sevm 2).toNat) := by
        simp [primaryFlowAtom, hnonempty, hselector,
          transferFromSelector_ne_depositSelector,
          transferFromSelector_ne_depositToSelector,
          transferFromSelector_ne_depositToAndCallSelector,
          transferFromSelector_ne_transferSelector,
          transferFromSelector_ne_transferAndCallSelector, hto]
      unfold Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      rcases frame with ⟨pc, e, pre, out, run, committed⟩
      cases out with
      | error err => simp [Execution.commits] at committed
      | ok post =>
          have hpc : pc = 0 := context.root.1
          subst pc
          apply Exec.Frame.CompiledBodyEthAccounting.flow action haction
          have hatom : primaryFlowAtom e = some
              (.transfer (Sevm.argWord e 0) (Sevm.argWord e 1)
                (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toAdr
                (Sevm.argWord e 2).toNat) := by
            simp [primaryFlowAtom, hnonempty, hselector,
              transferFromSelector_ne_depositSelector,
              transferFromSelector_ne_depositToSelector,
              transferFromSelector_ne_depositToAndCallSelector,
              transferFromSelector_ne_transferSelector,
              transferFromSelector_ne_transferAndCallSelector,
              hto]
          have hactionAtom : action.atom =
              .transfer (Sevm.argWord e 0) (Sevm.argWord e 1)
                (Sevm.argWord e 0).toAdr (Sevm.argWord e 1).toAdr
                (Sevm.argWord e 2).toNat := by
            unfold Exec.Frame.flowAction? at haction
            rw [if_pos context.invocation, hatom] at haction
            exact congrArg FlowAction.atom
              (Option.some.inj haction).symm
          have heffect := (weth10_transferFrom_successEffect dp
            context.memory_wf context.memory_reads_empty run
            context.invocation.2.2.2
            (by simpa only [transferFromSelector] using hselector)
            hnonempty).2
          rcases heffect with ⟨corePre, hallowance, hcore⟩
          rcases hcore with hzero | hnonzero
          · exact (hto hzero.1).elim
          · rcases hnonzero with ⟨_, _, _, _, _, _, _, hbalance, _⟩
            exact RichBodyEthAccounting.zeroSilent
              (by simp [FlowAction.bodyEthActions, hactionAtom])
              (by simp [FlowAtom.ethMint, hactionAtom])
              (by simp [FlowAtom.ethRedemption, hactionAtom])
              (hbalance.trans hallowance.2.2.1) chronology

/-- Exact body ETH accounting for the empty-calldata receive arm.  As for
`deposit()`, its ordinary mint is funded at message entry and the installed
body has neither an ETH balance effect nor a retained child. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_receive
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hempty : frame.sevm.data.length.toB256 = 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hdesc :
          Exec.Frame.descendantFlowActions dp ca
            (Exec.Frame.mk 0 e pre (.ok post) run committed) = [] :=
        Exec.Frame.descendantFlowActions_eq_nil_of_receive context hempty
      cases haction :
          Exec.Frame.flowAction? dp ca
            (Exec.Frame.mk 0 e pre (.ok post) run committed) with
      | none =>
          have hprimary : primaryFlowAtom e ≠ none := by
            simp [primaryFlowAtom, hempty]
          unfold Exec.Frame.flowAction? at haction
          rw [if_pos context.invocation] at haction
          cases hp : primaryFlowAtom e with
          | none => exact (hprimary hp).elim
          | some atom => simp [hp] at haction
      | some action =>
          apply Exec.Frame.CompiledBodyEthAccounting.flow action haction
          have hprimary : primaryFlowAtom e =
              some (.ordinaryMint e.caller.toB256 e.caller e.value.toNat) := by
            simp [primaryFlowAtom, hempty]
          have hatom : action.atom =
              .ordinaryMint e.caller.toB256 e.caller e.value.toNat := by
            unfold Exec.Frame.flowAction? at haction
            rw [if_pos context.invocation, hprimary] at haction
            exact congrArg FlowAction.atom (Option.some.inj haction).symm
          have heffect := receive_exec_effect dp context.memory_wf
            context.memory_reads_empty run context.invocation.2.2.2 hempty
          exact RichBodyEthAccounting.mintSilent hatom
            heffect.2.2.2.1 hdesc

/-- Exact body ETH accounting for the call-free payable `deposit()` leaf.
Its ordinary mint is funded at message entry; the installed body itself is
ETH-balance silent and has no retained children. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_deposit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hdesc :
          Exec.Frame.descendantFlowActions dp ca
            (Exec.Frame.mk 0 e pre (.ok post) run committed) = [] :=
        Exec.Frame.descendantFlowActions_eq_nil_of_deposit
          context hselector hnonempty
      cases haction :
          Exec.Frame.flowAction? dp ca
            (Exec.Frame.mk 0 e pre (.ok post) run committed) with
      | none =>
          have hprimary : primaryFlowAtom e ≠ none := by
            simp [primaryFlowAtom, hnonempty, hselector]
          unfold Exec.Frame.flowAction? at haction
          rw [if_pos context.invocation] at haction
          cases hp : primaryFlowAtom e with
          | none => exact (hprimary hp).elim
          | some atom => simp [hp] at haction
      | some action =>
          apply Exec.Frame.CompiledBodyEthAccounting.flow action haction
          have hprimary : primaryFlowAtom e =
              some (.ordinaryMint e.caller.toB256 e.caller e.value.toNat) := by
            simp [primaryFlowAtom, hnonempty, hselector]
          have hatom : action.atom =
              .ordinaryMint e.caller.toB256 e.caller e.value.toNat := by
            unfold Exec.Frame.flowAction? at haction
            rw [if_pos context.invocation, hprimary] at haction
            exact congrArg FlowAction.atom (Option.some.inj haction).symm
          have heffect := deposit_exec_effect dp context.memory_wf
            context.memory_reads_empty run context.invocation.2.2.2
            (by simpa only [depositSelector] using hselector) hnonempty
          exact RichBodyEthAccounting.mintSilent hatom
            heffect.2.2.2.1 hdesc

/-- Exact body ETH accounting for the call-free payable
`depositTo(address)` leaf. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_depositTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame with ⟨pc, e, pre, out, run, committed⟩
  cases out with
  | error err => simp [Execution.commits] at committed
  | ok post =>
      have hpc : pc = 0 := context.root.1
      subst pc
      have hdesc :
          Exec.Frame.descendantFlowActions dp ca
            (Exec.Frame.mk 0 e pre (.ok post) run committed) = [] :=
        Exec.Frame.descendantFlowActions_eq_nil_of_depositTo
          context hselector hnonempty
      cases haction :
          Exec.Frame.flowAction? dp ca
            (Exec.Frame.mk 0 e pre (.ok post) run committed) with
      | none =>
          have hprimary : primaryFlowAtom e ≠ none := by
            simp [primaryFlowAtom, hnonempty, hselector,
              depositToSelector_ne_depositSelector]
          unfold Exec.Frame.flowAction? at haction
          rw [if_pos context.invocation] at haction
          cases hp : primaryFlowAtom e with
          | none => exact (hprimary hp).elim
          | some atom => simp [hp] at haction
      | some action =>
          apply Exec.Frame.CompiledBodyEthAccounting.flow action haction
          have hprimary : primaryFlowAtom e = some
              (.ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
                e.value.toNat) := by
            simp [primaryFlowAtom, hnonempty, hselector,
              depositToSelector_ne_depositSelector]
          have hatom : action.atom =
              .ordinaryMint (Sevm.argWord e 0) (Sevm.argWord e 0).toAdr
                e.value.toNat := by
            unfold Exec.Frame.flowAction? at haction
            rw [if_pos context.invocation, hprimary] at haction
            exact congrArg FlowAction.atom (Option.some.inj haction).symm
          have heffect := depositTo_exec_effect dp context.memory_wf
            context.memory_reads_empty run context.invocation.2.2.2
            (by simpa only [depositToSelector] using hselector) hnonempty
          exact RichBodyEthAccounting.mintSilent hatom
            heffect.2.2.1 hdesc

/-- Exact body ETH accounting for payable `depositToAndCall(address,bytes)`.
The mint prefix is balance-silent inside the body, and the indexed retained
callback contributes its exact zero-value child ledger. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_depositToAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = depositToAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame.compiledDepositToAndCallChronology context hselector
      hnonempty with
    ⟨callbackPre, _hstorage, _hlogs, hbalance, hcode, _houtput,
      inputSize, input, callPre, callPost, parent, child, xl, pc,
      retained, callback, _rawCommits, _occurrence, chronology⟩
  have installedCallback : some (callbackPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [hcode]
    exact context.installed.1
  have hsumCallback : sum callbackPre.state.bal < 2 ^ 256 := by
    change sum (Devm.getBal callbackPre) < 2 ^ 256
    rw [hbalance]
    exact hsum
  rcases callback.zeroValueCallbackEthSegment retained installedCallback
      hdeeper hsumCallback with ⟨callbackSegment, retainedFlowEq⟩
  rcases callbackSegment with
    ⟨innerCallPre, innerCallPost, call, hcallbackPreBalance,
      hpostBalance⟩
  let callbackForFrame : ZeroValueCallbackEthSegment dp ca frame.sevm
      frame.pre frame.post :=
    ⟨innerCallPre, innerCallPost, call,
      hbalance.symm.trans hcallbackPreBalance, hpostBalance⟩
  have hprimary : primaryFlowAtom frame.sevm = some
      (.ordinaryMint (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      depositToAndCallSelector_ne_depositSelector,
      depositToAndCallSelector_ne_depositToSelector]
  cases haction : frame.flowAction? dp ca with
  | none =>
      unfold Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      apply Exec.Frame.CompiledBodyEthAccounting.flow action haction
      have hatom : action.atom =
          .ordinaryMint (Sevm.argWord frame.sevm 0)
            (Sevm.argWord frame.sevm 0).toAdr frame.sevm.value.toNat := by
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        exact congrArg FlowAction.atom (Option.some.inj haction).symm
      apply RichBodyEthAccounting.mintCallback hatom callbackForFrame
      calc
        frame.descendantFlowActions dp ca =
            retained.flowActions dp ca := by
          simpa only [List.nil_append] using chronology
        _ = callbackForFrame.call.trace.retained.flowActions dp ca := by
          simpa only [callbackForFrame] using retainedFlowEq.symm

/-- Exact no-root-flow ETH accounting for `approveAndCall`.  The approval
prefix is balance-silent, and the indexed retained callback contributes its
exact zero-value child ledger. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_approveAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = approveAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame.compiledApproveAndCallChronology context hselector
      hnonempty with
    ⟨callbackPre, _hstorage, _hlogs, hbalance, hcode, _houtput,
      inputSize, input, callPre, callPost, parent, child, xl, pc,
      retained, callback, _rawCommits, _occurrence, chronology⟩
  have installedCallback : some (callbackPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [hcode]
    exact context.installed.1
  have hsumCallback : sum callbackPre.state.bal < 2 ^ 256 := by
    change sum (Devm.getBal callbackPre) < 2 ^ 256
    rw [hbalance]
    exact hsum
  rcases callback.zeroValueCallbackEthSegment retained installedCallback
      hdeeper hsumCallback with ⟨callbackSegment, retainedFlowEq⟩
  rcases callbackSegment with
    ⟨innerCallPre, innerCallPost, call, hcallbackPreBalance,
      hpostBalance⟩
  let callbackForFrame : ZeroValueCallbackEthSegment dp ca frame.sevm
      frame.pre frame.post :=
    ⟨innerCallPre, innerCallPost, call,
      hbalance.symm.trans hcallbackPreBalance, hpostBalance⟩
  have hnoPrimary : SelectsNoPrimaryFlow frame.sevm := by
    constructor <;> rw [hselector] <;> decide +kernel
  have classified := frame.flowAction_eq_none_of_selectsNoPrimaryFlow context
    hnoPrimary hnonempty
  apply Exec.Frame.CompiledBodyEthAccounting.noFlow classified
  apply NoFlowBodyEthAccounting.callback callbackForFrame
  calc
    frame.descendantFlowActions dp ca =
        retained.flowActions dp ca := by
      simpa only [List.nil_append] using chronology
    _ = callbackForFrame.call.trace.retained.flowActions dp ca := by
      simpa only [callbackForFrame] using retainedFlowEq.symm

/-- Premise-free exact body ETH accounting for `flashLoan`.  Its local token
credit and repayment are ETH-silent, while the chronology's exact retained
borrower callback contributes the only recursive ETH segment. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_flashLoan
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = flashLoanSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame.compiledFlashLoanChronology context hselector hnonempty with
    ⟨callbackPre, callbackPost, settlePre, burnPre, parent, child, xl, pc,
      retained, callback, _rawCommits, _occurrence, _hcredit, hprefixBal,
      hprefixCode, _hcallbackStor, hcallbackBal, _hcallbackCode,
      _hcallbackLogs, _hcallbackOutput, _hwfSettle, _hreadsSettle,
      _hsettle, _hsettleSilent, _hcover, _hdecrease, hsettlePostBal,
      _hsettlePostCode, _hburn, chronology⟩
  have installedCallback : some (callbackPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [← congrFun hprefixCode ca]
    exact context.installed.1
  have hsumCallback : sum callbackPre.state.bal < 2 ^ 256 := by
    change sum (Devm.getBal callbackPre) < 2 ^ 256
    rw [← hprefixBal]
    exact hsum
  rcases callback.zeroValueCallbackEthSegment retained installedCallback
      hdeeper hsumCallback with ⟨callbackSegment, retainedFlowEq⟩
  rcases callbackSegment with
    ⟨innerCallPre, innerCallPost, call, hcallbackPreBalance,
      hcallbackPostBalance⟩
  let callbackForFrame : ZeroValueCallbackEthSegment dp ca frame.sevm
      frame.pre frame.post :=
    ⟨innerCallPre, innerCallPost, call,
      hprefixBal.trans hcallbackPreBalance,
      (hcallbackBal.trans hsettlePostBal).symm.trans
        hcallbackPostBalance⟩
  have hprimary : primaryFlowAtom frame.sevm = some
      (.flashPair (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 2).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      flashLoanSelector_ne_depositSelector,
      flashLoanSelector_ne_depositToSelector,
      flashLoanSelector_ne_depositToAndCallSelector,
      flashLoanSelector_ne_transferSelector,
      flashLoanSelector_ne_transferAndCallSelector,
      flashLoanSelector_ne_transferFromSelector,
      flashLoanSelector_ne_withdrawSelector,
      flashLoanSelector_ne_withdrawToSelector,
      flashLoanSelector_ne_withdrawFromSelector]
  cases haction : frame.flowAction? dp ca with
  | none =>
      unfold Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      apply Exec.Frame.CompiledBodyEthAccounting.flow action haction
      have hatom : action.atom =
          .flashPair (Sevm.argWord frame.sevm 0)
            (Sevm.argWord frame.sevm 0).toAdr
            (Sevm.argWord frame.sevm 2).toNat := by
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        exact congrArg FlowAction.atom (Option.some.inj haction).symm
      apply RichBodyEthAccounting.zeroCallback
        (callback := callbackForFrame)
      · simp [FlowAction.bodyEthActions, hatom]
      · simp [FlowAtom.ethMint, hatom]
      · simp [FlowAtom.ethRedemption, hatom]
      · calc
          frame.descendantFlowActions dp ca =
              retained.flowActions dp ca := by
            simpa only [List.nil_append] using chronology
          _ = callbackForFrame.call.trace.retained.flowActions dp ca := by
            simpa only [callbackForFrame] using retainedFlowEq.symm

/-- Internal adapter from one exact retained value-redemption chronology to
body ETH accounting.  The accepted child pays for the root redemption while
the explicit balance-silent prefix and suffix preserve its exact ledger. -/
private theorem Exec.Frame.compiledBodyEthAccounting_of_valueRedemption
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction} {rawSource : B256} {source ethRecipient : Adr}
    {amount target : B256} {callPre guardPost : Devm}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = some action)
    (hatom : action.atom =
      .redemption rawSource source ethRecipient amount.toNat)
    (trace : AcceptedValueCallTrace frame.sevm target amount
      callPre guardPost)
    (burn : BurnCallPrefix frame.sevm frame.pre callPre guardPost
      source amount target)
    (hguardBalance : Devm.getBal guardPost = Devm.getBal frame.post)
    (chronology : frame.descendantFlowActions dp ca =
      trace.retained.retained.flowActions dp ca)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  have installedCall : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [burn.2.2.2.2.2.1]
    exact context.installed.1
  have hsumCall : sum callPre.state.bal < 2 ^ 256 := by
    change sum (Devm.getBal callPre) < 2 ^ 256
    rw [burn.2.2.2.2.1]
    exact hsum
  have witness := trace.redemptionEthBound context.invocation.2.1
    installedCall hatom hdeeper hsumCall
  let accepted : AcceptedRedemptionEthSegment dp ca frame.sevm action
      callPre guardPost :=
    ⟨target, amount, trace,
      by simp [FlowAction.bodyEthActions, hatom], witness.bound⟩
  let segment : RedemptionEthSegment dp ca frame.sevm action
      frame.pre frame.post :=
    ⟨callPre, guardPost, accepted, burn.2.2.2.2.1.symm,
      hguardBalance.symm⟩
  apply Exec.Frame.CompiledBodyEthAccounting.flow action classified
  exact RichBodyEthAccounting.redemption segment (by
    simpa only [segment, accepted] using chronology)

/-- Internal ETH adapter for a delegated redemption after the allowance
wrapper.  The wrapper may update allowance storage and logs, but its exact
balance/code observations connect the literal `ownPre` burn to frame entry. -/
private theorem Exec.Frame.compiledBodyEthAccounting_of_allowanceValueRedemption
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    {action : FlowAction} {rawSource : B256} {source ethRecipient : Adr}
    {amount target : B256} {ownPre callPre guardPost : Devm}
    (context : frame.AuthenticContext dp ca)
    (classified : frame.flowAction? dp ca = some action)
    (hatom : action.atom =
      .redemption rawSource source ethRecipient amount.toNat)
    (entry : AllowancePrefixObservations frame.sevm frame.pre ownPre)
    (trace : AcceptedValueCallTrace frame.sevm target amount
      callPre guardPost)
    (burn : BurnCallPrefix frame.sevm ownPre callPre guardPost
      source amount target)
    (hguardBalance : Devm.getBal guardPost = Devm.getBal frame.post)
    (chronology : frame.descendantFlowActions dp ca =
      trace.retained.retained.flowActions dp ca)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  have installedCall : some (callPre.getCode ca).toList =
      Prog.compile (weth10 dp) := by
    rw [burn.2.2.2.2.2.1, ← entry.code]
    exact context.installed.1
  have hsumCall : sum callPre.state.bal < 2 ^ 256 := by
    change sum (Devm.getBal callPre) < 2 ^ 256
    rw [burn.2.2.2.2.1, ← entry.balance]
    exact hsum
  have witness := trace.redemptionEthBound context.invocation.2.1
    installedCall hatom hdeeper hsumCall
  let accepted : AcceptedRedemptionEthSegment dp ca frame.sevm action
      callPre guardPost :=
    ⟨target, amount, trace,
      by simp [FlowAction.bodyEthActions, hatom], witness.bound⟩
  let segment : RedemptionEthSegment dp ca frame.sevm action
      frame.pre frame.post :=
    ⟨callPre, guardPost, accepted,
      entry.balance.trans burn.2.2.2.2.1.symm,
      hguardBalance.symm⟩
  apply Exec.Frame.CompiledBodyEthAccounting.flow action classified
  exact RichBodyEthAccounting.redemption segment (by
    simpa only [segment, accepted] using chronology)

/-- Premise-free exact body ETH accounting for `withdraw(uint256)`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_withdraw
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.caller (Sevm.argWord frame.sevm 0).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      withdrawSelector_ne_depositSelector,
      withdrawSelector_ne_depositToSelector,
      withdrawSelector_ne_depositToAndCallSelector,
      withdrawSelector_ne_transferSelector,
      withdrawSelector_ne_transferAndCallSelector,
      withdrawSelector_ne_transferFromSelector]
  cases haction : frame.flowAction? dp ca with
  | none =>
      unfold Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have hactionAtom : action.atom =
          .redemption frame.sevm.caller.toB256 frame.sevm.caller
            frame.sevm.caller (Sevm.argWord frame.sevm 0).toNat := by
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        exact congrArg FlowAction.atom (Option.some.inj haction).symm
      rcases frame.compiledWithdrawChronology context hselector hnonempty with
        ⟨callPre, guardPost, trace, burn, _hslot, _hcommits,
          _hoccurrence, _hguardStor, hguardBalance, _hguardCode,
          _hguardLogs, chronology⟩
      refine frame.compiledBodyEthAccounting_of_valueRedemption
        (rawSource := frame.sevm.caller.toB256)
        (source := frame.sevm.caller)
        (ethRecipient := frame.sevm.caller)
        (amount := Sevm.argWord frame.sevm 0)
        (target := frame.sevm.caller.toB256)
        (callPre := callPre) (guardPost := guardPost)
        context haction hactionAtom trace burn hguardBalance ?_ hdeeper hsum
      simpa only [List.nil_append] using chronology

/-- Premise-free exact body ETH accounting for
`withdrawTo(address,uint256)`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_withdrawTo
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawToSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      withdrawToSelector_ne_depositSelector,
      withdrawToSelector_ne_depositToSelector,
      withdrawToSelector_ne_depositToAndCallSelector,
      withdrawToSelector_ne_transferSelector,
      withdrawToSelector_ne_transferAndCallSelector,
      withdrawToSelector_ne_transferFromSelector,
      withdrawToSelector_ne_withdrawSelector]
  cases haction : frame.flowAction? dp ca with
  | none =>
      unfold Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have hactionAtom : action.atom =
          .redemption frame.sevm.caller.toB256 frame.sevm.caller
            (Sevm.argWord frame.sevm 0).toAdr
            (Sevm.argWord frame.sevm 1).toNat := by
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        exact congrArg FlowAction.atom (Option.some.inj haction).symm
      rcases frame.compiledWithdrawToChronology context hselector
          hnonempty with
        ⟨callPre, guardPost, trace, burn, _hslot, _hcommits,
          _hoccurrence, _hguardStor, hguardBalance, _hguardCode,
          _hguardLogs, chronology⟩
      refine frame.compiledBodyEthAccounting_of_valueRedemption
        (rawSource := frame.sevm.caller.toB256)
        (source := frame.sevm.caller)
        (ethRecipient := (Sevm.argWord frame.sevm 0).toAdr)
        (amount := Sevm.argWord frame.sevm 1)
        (target := Sevm.argWord frame.sevm 0)
        (callPre := callPre) (guardPost := guardPost)
        context haction hactionAtom trace burn hguardBalance ?_ hdeeper hsum
      simpa only [List.nil_append] using chronology

/-- Premise-free exact body ETH accounting for the zero-recipient
`transfer(address,uint256)` redemption arm. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_transferZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 0 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption frame.sevm.caller.toB256 frame.sevm.caller
        frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      transferSelector_ne_depositSelector,
      transferSelector_ne_depositToSelector,
      transferSelector_ne_depositToAndCallSelector, hto]
  cases haction : frame.flowAction? dp ca with
  | none =>
      unfold Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have hactionAtom : action.atom =
          .redemption frame.sevm.caller.toB256 frame.sevm.caller
            frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat := by
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        exact congrArg FlowAction.atom (Option.some.inj haction).symm
      rcases frame.compiledTransferZeroChronology context hselector
          hnonempty hto with
        ⟨callPre, guardPost, trace, burn, _hslot, _hcommits,
          _hoccurrence, _hguardStor, hguardBalance, _hguardCode,
          _hguardLogs, chronology⟩
      refine frame.compiledBodyEthAccounting_of_valueRedemption
        (rawSource := frame.sevm.caller.toB256)
        (source := frame.sevm.caller)
        (ethRecipient := frame.sevm.caller)
        (amount := Sevm.argWord frame.sevm 1)
        (target := frame.sevm.caller.toB256)
        (callPre := callPre) (guardPost := guardPost)
        context haction hactionAtom trace burn hguardBalance ?_ hdeeper hsum
      simpa only [List.nil_append] using chronology

/-- Premise-free exact body ETH accounting for the zero-recipient delegated
`transferFrom` redemption arm. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_transferFromZero
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hto : Sevm.argWord frame.sevm 1 = 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr frame.sevm.caller
        (Sevm.argWord frame.sevm 2).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      transferFromSelector_ne_depositSelector,
      transferFromSelector_ne_depositToSelector,
      transferFromSelector_ne_depositToAndCallSelector,
      transferFromSelector_ne_transferSelector,
      transferFromSelector_ne_transferAndCallSelector, hto]
  cases haction : frame.flowAction? dp ca with
  | none =>
      unfold Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have hactionAtom : action.atom =
          .redemption (Sevm.argWord frame.sevm 0)
            (Sevm.argWord frame.sevm 0).toAdr frame.sevm.caller
            (Sevm.argWord frame.sevm 2).toNat := by
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        exact congrArg FlowAction.atom (Option.some.inj haction).symm
      rcases frame.compiledTransferFromZeroChronology context hselector
          hnonempty hto with
        ⟨ownPre, entry, callPre, guardPost, trace, burn, _hslot,
          _hcommits, _hoccurrence, _hguardStor, hguardBalance,
          _hguardCode, _hguardLogs, chronology⟩
      have hsource : (normalizedAddressArg frame.sevm 0).toAdr =
          (Sevm.argWord frame.sevm 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256_eth, toAdr_toB256]
      have burn' : BurnCallPrefix frame.sevm ownPre callPre guardPost
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 2) frame.sevm.caller.toB256 := by
        simpa only [hsource] using burn
      refine frame.compiledBodyEthAccounting_of_allowanceValueRedemption
        (rawSource := Sevm.argWord frame.sevm 0)
        (source := (Sevm.argWord frame.sevm 0).toAdr)
        (ethRecipient := frame.sevm.caller)
        (amount := Sevm.argWord frame.sevm 2)
        (target := frame.sevm.caller.toB256)
        (ownPre := ownPre) (callPre := callPre) (guardPost := guardPost)
        context haction hactionAtom entry trace burn' hguardBalance ?_
          hdeeper hsum
      simpa only [List.nil_append] using chronology

/-- Premise-free exact body ETH accounting for delegated
`withdrawFrom(address,address,uint256)`. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_withdrawFrom
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = withdrawFromSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  have hprimary : primaryFlowAtom frame.sevm = some
      (.redemption (Sevm.argWord frame.sevm 0)
        (Sevm.argWord frame.sevm 0).toAdr
        (Sevm.argWord frame.sevm 1).toAdr
        (Sevm.argWord frame.sevm 2).toNat) := by
    simp [primaryFlowAtom, hnonempty, hselector,
      withdrawFromSelector_ne_depositSelector,
      withdrawFromSelector_ne_depositToSelector,
      withdrawFromSelector_ne_depositToAndCallSelector,
      withdrawFromSelector_ne_transferSelector,
      withdrawFromSelector_ne_transferAndCallSelector,
      withdrawFromSelector_ne_transferFromSelector,
      withdrawFromSelector_ne_withdrawSelector,
      withdrawFromSelector_ne_withdrawToSelector]
  cases haction : frame.flowAction? dp ca with
  | none =>
      unfold Exec.Frame.flowAction? at haction
      rw [if_pos context.invocation, hprimary] at haction
      simp at haction
  | some action =>
      have hactionAtom : action.atom =
          .redemption (Sevm.argWord frame.sevm 0)
            (Sevm.argWord frame.sevm 0).toAdr
            (Sevm.argWord frame.sevm 1).toAdr
            (Sevm.argWord frame.sevm 2).toNat := by
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        exact congrArg FlowAction.atom (Option.some.inj haction).symm
      rcases frame.compiledWithdrawFromChronology context hselector
          hnonempty with
        ⟨ownPre, entry, callPre, guardPost, trace, burn, _hslot,
          _hcommits, _hoccurrence, _hguardStor, hguardBalance,
          _hguardCode, _hguardLogs, chronology⟩
      have hsource : (normalizedAddressArg frame.sevm 0).toAdr =
          (Sevm.argWord frame.sevm 0).toAdr := by
        rw [normalizedAddressArg_eq_toAdr_toB256_eth, toAdr_toB256]
      have burn' : BurnCallPrefix frame.sevm ownPre callPre guardPost
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 2) (Sevm.argWord frame.sevm 1) := by
        simpa only [hsource] using burn
      refine frame.compiledBodyEthAccounting_of_allowanceValueRedemption
        (rawSource := Sevm.argWord frame.sevm 0)
        (source := (Sevm.argWord frame.sevm 0).toAdr)
        (ethRecipient := (Sevm.argWord frame.sevm 1).toAdr)
        (amount := Sevm.argWord frame.sevm 2)
        (target := Sevm.argWord frame.sevm 1)
        (ownPre := ownPre) (callPre := callPre) (guardPost := guardPost)
        context haction hactionAtom entry trace burn' hguardBalance ?_
          hdeeper hsum
      simpa only [List.nil_append] using chronology

/-- Premise-free exact body ETH accounting for both `transferAndCall` arms.
The raw-zero arm composes the retained value redemption before the retained
zero-value ERC-677 callback; the nonzero arm contributes only that callback. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_transferAndCall
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = transferAndCallSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame.compiledTransferAndCallChronology context hselector
      hnonempty with hzero | hnonzero
  · rcases hzero with
      ⟨hraw, callPre, callbackPre, trace, burn, _hslot, _hcommits,
        _hoccurrence, tokenChronology⟩
    rcases tokenChronology with
      ⟨_inputSize, _input, _callbackCallPre, _callbackCallPost,
        _parent, _child, _xl, _pc, retained, callback, _callbackCommits,
        _callbackOccurrence, chronology⟩
    have installedCall : some (callPre.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [burn.2.2.2.2.2.1]
      exact context.installed.1
    have hsumCall : sum callPre.state.bal < 2 ^ 256 := by
      change sum (Devm.getBal callPre) < 2 ^ 256
      rw [burn.2.2.2.2.1]
      exact hsum
    have hprimary : primaryFlowAtom frame.sevm = some
        (.redemption frame.sevm.caller.toB256 frame.sevm.caller
          frame.sevm.caller (Sevm.argWord frame.sevm 1).toNat) := by
      simp [primaryFlowAtom, hnonempty, hselector,
        transferAndCallSelector_ne_depositSelector,
        transferAndCallSelector_ne_depositToSelector,
        transferAndCallSelector_ne_depositToAndCallSelector, hraw]
    cases haction : frame.flowAction? dp ca with
    | none =>
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        simp at haction
    | some action =>
        have hactionAtom : action.atom =
            .redemption frame.sevm.caller.toB256 frame.sevm.caller
              frame.sevm.caller
              (Sevm.argWord frame.sevm 1).toNat := by
          unfold Exec.Frame.flowAction? at haction
          rw [if_pos context.invocation, hprimary] at haction
          exact congrArg FlowAction.atom (Option.some.inj haction).symm
        have valueWitness := trace.redemptionEthBound
          context.invocation.2.1 installedCall hactionAtom hdeeper hsumCall
        let accepted : AcceptedRedemptionEthSegment dp ca frame.sevm
            action callPre callbackPre :=
          ⟨frame.sevm.caller.toB256, Sevm.argWord frame.sevm 1, trace,
            by simp [FlowAction.bodyEthActions, hactionAtom],
            valueWitness.bound⟩
        let redemption : RedemptionEthSegment dp ca frame.sevm action
            frame.pre callbackPre :=
          ⟨callPre, callbackPre, accepted,
            burn.2.2.2.2.1.symm, rfl⟩
        have installedCallback : some (callbackPre.getCode ca).toList =
            Prog.compile (weth10 dp) := by
          rw [trace.guard_code_eq installedCall]
          exact installedCall
        have hsumCallback : sum callbackPre.state.bal < 2 ^ 256 :=
          lt_of_le_of_lt trace.guard_sum_le hsumCall
        rcases callback.zeroValueCallbackEthSegment retained
            installedCallback hdeeper hsumCallback with
          ⟨callbackSegment, retainedFlowEq⟩
        apply Exec.Frame.CompiledBodyEthAccounting.flow action haction
        apply RichBodyEthAccounting.redemptionThenCallback redemption
          callbackSegment
        calc
          frame.descendantFlowActions dp ca =
              trace.retained.retained.flowActions dp ca ++
                retained.flowActions dp ca := chronology
          _ = redemption.accepted.trace.retained.retained.flowActions
                dp ca ++
              callbackSegment.call.trace.retained.flowActions dp ca := by
            simp only [redemption, accepted]
            rw [retainedFlowEq]
  · rcases hnonzero with
      ⟨hraw, recipient, callbackPre, _hrecipient, _htransfer,
        _hflash, _hlogs, hbalance, hcode, _houtput, tokenChronology⟩
    rcases tokenChronology with
      ⟨_inputSize, _input, _callbackCallPre, _callbackCallPost,
        _parent, _child, _xl, _pc, retained, callback, _callbackCommits,
        _callbackOccurrence, chronology⟩
    have installedCallback : some (callbackPre.getCode ca).toList =
        Prog.compile (weth10 dp) := by
      rw [hcode]
      exact context.installed.1
    have hsumCallback : sum callbackPre.state.bal < 2 ^ 256 := by
      change sum (Devm.getBal callbackPre) < 2 ^ 256
      rw [hbalance]
      exact hsum
    rcases callback.zeroValueCallbackEthSegment retained installedCallback
        hdeeper hsumCallback with ⟨callbackSegment, retainedFlowEq⟩
    rcases callbackSegment with
      ⟨innerCallPre, innerCallPost, call, hcallbackPreBalance,
        hpostBalance⟩
    let callbackForFrame : ZeroValueCallbackEthSegment dp ca frame.sevm
        frame.pre frame.post :=
      ⟨innerCallPre, innerCallPost, call,
        hbalance.symm.trans hcallbackPreBalance, hpostBalance⟩
    have hprimary : primaryFlowAtom frame.sevm = some
        (.transfer frame.sevm.caller.toB256
          (Sevm.argWord frame.sevm 0) frame.sevm.caller
          (Sevm.argWord frame.sevm 0).toAdr
          (Sevm.argWord frame.sevm 1).toNat) := by
      simp [primaryFlowAtom, hnonempty, hselector,
        transferAndCallSelector_ne_depositSelector,
        transferAndCallSelector_ne_depositToSelector,
        transferAndCallSelector_ne_depositToAndCallSelector, hraw]
    cases haction : frame.flowAction? dp ca with
    | none =>
        unfold Exec.Frame.flowAction? at haction
        rw [if_pos context.invocation, hprimary] at haction
        simp at haction
    | some action =>
        have hactionAtom : action.atom =
            .transfer frame.sevm.caller.toB256
              (Sevm.argWord frame.sevm 0) frame.sevm.caller
              (Sevm.argWord frame.sevm 0).toAdr
              (Sevm.argWord frame.sevm 1).toNat := by
          unfold Exec.Frame.flowAction? at haction
          rw [if_pos context.invocation, hprimary] at haction
          exact congrArg FlowAction.atom (Option.some.inj haction).symm
        apply Exec.Frame.CompiledBodyEthAccounting.flow action haction
        apply RichBodyEthAccounting.zeroCallback
          (callback := callbackForFrame)
        · simp [FlowAction.bodyEthActions, hactionAtom]
        · simp [FlowAtom.ethMint, hactionAtom]
        · simp [FlowAtom.ethRedemption, hactionAtom]
        · calc
            frame.descendantFlowActions dp ca =
                retained.flowActions dp ca := by
              simpa only [List.nil_append] using chronology
            _ = callbackForFrame.call.trace.retained.flowActions
                  dp ca := by
              simpa only [callbackForFrame] using retainedFlowEq.symm

/-- Premise-free exact body ETH accounting for `permit`.  Empty and
rolled-back STATICCALL outcomes are balance-silent; the committing outcome
uses the exact retained zero-value child selected by compiled chronology. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_permit
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (hselector : Sevm.selector frame.sevm = permitSelector)
    (hnonempty : frame.sevm.data.length.toB256 ≠ 0)
    (hdeeper : ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out))
    (hsum : sum frame.pre.state.bal < 2 ^ 256) :
    frame.CompiledBodyEthAccounting dp ca := by
  rcases frame.compiledPermitChronology context hselector hnonempty with
    ⟨callPre, callPost, slot, selected, _occurrence, _operands,
      outcome, ownPrefix, ownSuffix, chronology⟩
  have htarget : frame.sevm.currentTarget = ca :=
    context.invocation.2.1
  have hnoPrimary : SelectsNoPrimaryFlow frame.sevm := by
    constructor <;> rw [hselector] <;> decide +kernel
  have classified := frame.flowAction_eq_none_of_selectsNoPrimaryFlow
    context hnoPrimary hnonempty
  cases outcome with
  | none own =>
      apply Exec.Frame.CompiledBodyEthAccounting.noFlow classified
      exact NoFlowBodyEthAccounting.silent
        (ownPrefix.balance.trans
          (own.balance.trans ownSuffix.balance)).symm chronology
  | rolledBack child trace rollsBack own =>
      apply Exec.Frame.CompiledBodyEthAccounting.noFlow classified
      exact NoFlowBodyEthAccounting.silent
        (ownPrefix.balance.trans
          (own.balance.trans ownSuffix.balance)).symm chronology
  | committed child trace commits =>
      have installedCall : some (callPre.getCode ca).toList =
          Prog.compile (weth10 dp) := by
        rw [← ownPrefix.code]
        exact context.installed.1
      have hsumCall : sum callPre.state.bal < 2 ^ 256 := by
        change sum (Devm.getBal callPre) < 2 ^ 256
        rw [← ownPrefix.balance]
        exact hsum
      let childTrace : ProcessMessageTrace trace.msg (.ok trace.childPost) :=
        ⟨_, .some child, trace.process⟩
      have hparent : callPre.state = trace.msg.benv.state :=
        trace.parentState.symm.trans trace.benvState.symm
      have htargetCode : trace.msg.currentTarget = ca →
          some trace.msg.code.toList = Prog.compile (weth10 dp) := by
        intro hmsgTarget
        have htargetCa : (1 : B256).toAdr = ca :=
          trace.target.symm.trans hmsgTarget
        exact callbackCode_eq_compiled_of_target_eq installedCall
          htargetCa trace.delegationResolution
      have htargetDirect : trace.msg.currentTarget = ca →
          trace.msg.codeAddress = some ca := by
        intro hmsgTarget
        have htargetCa : (1 : B256).toAdr = ca :=
          trace.target.symm.trans hmsgTarget
        exact trace.codeAddress.trans (congrArg some htargetCa)
      have rawBound := childTrace.ethBound_of_zeroDeeper hparent
        trace.depth installedCall htargetCode htargetDirect trace.value
          hdeeper hsumCall
      have hresumeState : callPost.state = trace.childPost.state :=
        Resume.call_state trace.resume
      have childBound : EthBound ca callPre.state callPost.state
          (Exec.flowActions dp ca child) := by
        unfold EthBound at rawBound ⊢
        rw [hresumeState]
        simpa only [childTrace, RetainedXlot.flowActions] using rawBound
      apply Exec.Frame.CompiledBodyEthAccounting.noFlow classified
      exact NoFlowBodyEthAccounting.staticCallback ownPrefix.balance
        childBound ownSuffix.balance.symm chronology

/-- Exact ETH dispatcher for all fifteen closed non-flow selectors.  The root
classification is derived from the selector inventory rather than accepted
as an extra branch premise. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_callFreeNoFlowBranch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (branch : frame.CallFreeNoFlowStorageBranch) :
    frame.CompiledBodyEthAccounting dp ca := by
  have classified : frame.flowAction? dp ca = none :=
    frame.flowAction_eq_none_of_selectsNoPrimaryFlow context
      branch.selectsNoPrimaryFlow branch.nonempty
  cases branch with
  | name nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_name
        context classified selected nonempty
  | approve nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_approve
        context classified selected nonempty
  | totalSupply nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_totalSupply
        context classified selected nonempty
  | permitTypehash nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_permitTypehash
        context classified selected nonempty
  | decimals nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_decimals
        context classified selected nonempty
  | domainSeparator nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_domainSeparator
        context classified selected nonempty
  | maxFlashLoan nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_maxFlashLoan
        context classified selected nonempty
  | balanceOf nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_balanceOf
        context classified selected nonempty
  | nonces nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_nonces
        context classified selected nonempty
  | callbackSuccess nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_callbackSuccess
        context classified selected nonempty
  | flashMinted nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_flashMinted
        context classified selected nonempty
  | symbol nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_symbol
        context classified selected nonempty
  | deploymentChainId nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_deploymentChainId
        context classified selected nonempty
  | flashFee nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_flashFee
        context classified selected nonempty
  | allowance nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_allowance
        context classified selected nonempty

/-- Exact ETH dispatcher for every already-closed call-free flow/no-flow
branch. -/
theorem Exec.Frame.compiledBodyEthAccounting_of_callFreeBranch
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (context : frame.AuthenticContext dp ca)
    (branch : frame.CallFreeStorageBranch) :
    frame.CompiledBodyEthAccounting dp ca := by
  cases branch with
  | receive empty =>
      exact frame.compiledBodyEthAccounting_of_receive context empty
  | deposit nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_deposit
        context selected nonempty
  | depositTo nonempty selected =>
      exact frame.compiledBodyEthAccounting_of_depositTo
        context selected nonempty
  | transferNonzero nonempty selected recipient =>
      have hprimary : primaryFlowAtom frame.sevm = some
          (.transfer frame.sevm.caller.toB256
            (Sevm.argWord frame.sevm 0) frame.sevm.caller
            (Sevm.argWord frame.sevm 0).toAdr
            (Sevm.argWord frame.sevm 1).toNat) := by
        simp [primaryFlowAtom, nonempty, selected,
          transferSelector_ne_depositSelector,
          transferSelector_ne_depositToSelector,
          transferSelector_ne_depositToAndCallSelector, recipient]
      cases classified : frame.flowAction? dp ca with
      | none =>
          unfold Exec.Frame.flowAction? at classified
          rw [if_pos context.invocation, hprimary] at classified
          simp at classified
      | some action =>
          exact frame.compiledBodyEthAccounting_of_transferNonzero
            context classified selected nonempty recipient
  | transferFromNonzero nonempty selected recipient =>
      exact frame.compiledBodyEthAccounting_of_transferFromNonzero
        context selected nonempty recipient
        (frame.descendantFlowActions_eq_nil_of_transferFromNonzero
          context selected nonempty recipient)
  | noFlow noFlow =>
      exact frame.compiledBodyEthAccounting_of_callFreeNoFlowBranch
        context noFlow

theorem Exec.Frame.CompiledBodyEthAccounting.bound
    {dp : DeployParams} {ca : Adr} {frame : Exec.Frame}
    (accounting : frame.CompiledBodyEthAccounting dp ca) :
    EthBound ca frame.pre.state frame.post.state
      (Exec.bodyEthActions dp ca frame.run frame.committed) := by
  rw [frame.bodyEthActions_eq]
  cases accounting with
  | flow action classified body =>
      rw [classified]
      exact body.bound
  | noFlow classified body =>
      rw [classified]
      simpa only [flowActionBodyEthActions, List.nil_append] using body.bound

/-- This is the final selector-facing interface: construct exact operational
body accounting for each authentic compiled frame, using only strong-depth
child soundness and the non-wrapping world-sum bound. -/
def CompiledFrameBodyEthAccountingHandler
    (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ (frame : Exec.Frame),
    frame.AuthenticContext dp ca →
    ForallDeeperAt frame.sevm.depth ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out) →
    sum frame.pre.state.bal < 2 ^ 256 →
    frame.CompiledBodyEthAccounting dp ca

/-- Premise-free exact body ETH accounting handler for every authentic
compiled WETH10 frame. -/
theorem compiledFrameBodyEthAccountingHandler
    (dp : DeployParams) (ca : Adr) :
    CompiledFrameBodyEthAccountingHandler dp ca := by
  intro frame context hdeeper hsum
  rcases frame.callFreeStorageBranch_or_remaining context with
      closed | openCase
  · exact frame.compiledBodyEthAccounting_of_callFreeBranch
      context closed
  · cases openCase with
    | depositToAndCall nonempty selected =>
        exact frame.compiledBodyEthAccounting_of_depositToAndCall
          context selected nonempty hdeeper hsum
    | transferZero nonempty selected recipient =>
        exact frame.compiledBodyEthAccounting_of_transferZero
          context selected nonempty recipient hdeeper hsum
    | transferAndCall nonempty selected =>
        exact frame.compiledBodyEthAccounting_of_transferAndCall
          context selected nonempty hdeeper hsum
    | transferFromZero nonempty selected recipient =>
        exact frame.compiledBodyEthAccounting_of_transferFromZero
          context selected nonempty recipient hdeeper hsum
    | withdraw nonempty selected =>
        exact frame.compiledBodyEthAccounting_of_withdraw
          context selected nonempty hdeeper hsum
    | withdrawTo nonempty selected =>
        exact frame.compiledBodyEthAccounting_of_withdrawTo
          context selected nonempty hdeeper hsum
    | withdrawFrom nonempty selected =>
        exact frame.compiledBodyEthAccounting_of_withdrawFrom
          context selected nonempty hdeeper hsum
    | flashLoan nonempty selected =>
        exact frame.compiledBodyEthAccounting_of_flashLoan
          context selected nonempty hdeeper hsum
    | approveAndCall nonempty selected =>
        exact frame.compiledBodyEthAccounting_of_approveAndCall
          context selected nonempty hdeeper hsum
    | permit nonempty selected =>
        exact frame.compiledBodyEthAccounting_of_permit
          context selected nonempty hdeeper hsum

/-- The single compiled-program handler expected by the generic recursion.
It receives the exact `Prog.Run` and the strong-depth hypotheses generated by
`lift_core`, but must prove the action-labelled endpoint for the concrete
`Exec` witness supplied to the predicate. -/
def CompiledBodyEthHandler (dp : DeployParams) (ca : Adr) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm},
    Prog.Run sevm pre (weth10 dp) post →
    sevm.currentTarget = ca →
    ForallDeeperAt sevm.depth ca (weth10 dp)
      (fun pc s d out _ => Exec.CoreEthSound dp ca pc s d out) →
    ∀ (run : Exec 0 sevm pre (.ok post))
      (hcommit : Execution.commits (.ok post) = true),
      Prog.At (weth10 dp) ca 0 sevm pre →
      (sevm.currentTarget = ca →
        Exec.Frame.IsRoot (Exec.Frame.ofRun run hcommit) ∧
        sevm.codeAddress = some ca) →
      sum pre.state.bal < 2 ^ 256 →
      EthBound ca pre.state post.state
        (Exec.bodyEthActions dp ca run hcommit)

/-- Root/direct premises reconstruct the authentic frame context, after which
the selector-facing operational witness closes the installed body handler. -/
theorem CompiledFrameBodyEthAccountingHandler.compiledBodyEthHandler
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledFrameBodyEthAccountingHandler dp ca) :
    CompiledBodyEthHandler dp ca := by
  intro sevm pre post _hrun htarget hdeeper run hcommit installed rootDirect
    hsum
  let frame := Exec.Frame.ofRun run hcommit
  have hrootDirect := rootDirect htarget
  have context : frame.AuthenticContext dp ca := by
    refine ⟨hrootDirect.1, ?_, installed⟩
    refine ⟨rfl, htarget, hrootDirect.2, ?_⟩
    exact (installed.2 htarget).1
  exact (handler frame context hdeeper hsum).bound

/-- Premise-free compiled-program ETH handler consumed by recursion. -/
theorem compiledBodyEthHandler
    (dp : DeployParams) (ca : Adr) :
    CompiledBodyEthHandler dp ca :=
  (compiledFrameBodyEthAccountingHandler dp ca).compiledBodyEthHandler

/-- Failed raw executions cannot satisfy the committed premise, regardless of
instruction kind or program location. -/
theorem Exec.CoreEthSound.error
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    {error : EvmError × Devm} :
    Exec.CoreEthSound dp ca pc sevm pre (.error error) := by
  intro run hcommit
  simp [Execution.commits] at hcommit

/-- Foreign non-recursive step handler for `lift_core`.  The proof uses the
actual step relation to distinguish a continuation from a no-slot settled
message, and `Exec.unique` aligns that reconstructed derivation with the
proof-indexed public action list. -/
theorem Exec.CoreEthSound.nextNone
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (hstep : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (hne : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreEthSound dp ca (pc + n.size) sevm inter out) :
    Exec.CoreEthSound dp ca pc sevm pre out := by
  intro run hcommit hatp _ hsum
  have hhead := Ninst.foreignNoneEthBound hstep hne hsum
  have hsumInter : sum inter.state.bal < 2 ^ 256 := by
    have hnoninc := Ninst.balance_effect n
      ⟨.none, trivial, pc, hstep⟩
    exact lt_of_le_of_lt hnoninc hsum
  have hcode : inter.getCode ca = pre.getCode ca := by
    have hrel := Ninst.codePreserve_effectRec n
      (xl := .none) trivial hstep
    have hpreserve : Devm.CodePreserve pre inter := by
      simpa [Execution.Rel, Outcome.Rel] using hrel
    exact hpreserve ca (fun hempty =>
      Prog.compile_ne_nil (hatp.1.symm.trans (congrArg some hempty)))
  have hatpInter : Prog.At (weth10 dp) ca
      (pc + n.size) sevm inter := by
    refine ⟨?_, fun htarget => (hne htarget).elim⟩
    rw [hcode]
    exact hatp.1
  have htail := ih next hcommit hatpInter
    (fun htarget => (hne htarget).elim) hsumInter
  have hbound := hhead.trans htail
  rw [Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
      next hcommit hne] at hbound
  cases hs : Ninst.step ⟨pc, sevm, pre⟩ n with
  | halt ex =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨_, heq⟩
      cases heq
      exact False.elim (Ninst.step_ne_halt_ok hs)
  | cont pc' actual =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨_, heq⟩
      cases heq
      have hpc : pc' = pc + n.size := Ninst.step_cont_pc hs
      subst pc'
      have hevm : Evm.step ⟨pc, sevm, pre⟩ =
          .cont (pc + n.size) inter := by
        rw [Evm.step_next hat]
        exact hs
      have hcanonical : run = Exec.cont hevm next := Exec.unique _ _
      subst run
      rw [Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
          (Exec.cont hevm next) hcommit hne]
      unfold Exec.descendantActions at hbound ⊢
      simpa only [Exec.descendantFrames, List.nil_append] using hbound
  | spawn frame resume pc' =>
      simp only [Ninst.StepRun, hs, Step.Run] at hstep
      rcases hstep with ⟨result, hframe, hresume⟩
      have hpc : pc' = pc + n.size := Ninst.step_spawn_pc hs
      subst pc'
      have hevm : Evm.step ⟨pc, sevm, pre⟩ =
          .spawn frame resume (pc + n.size) := by
        rw [Evm.step_next hat]
        exact hs
      have hdone : ∃ result',
          frame.enter = .done result' ∧ result = result' := by
        unfold RunFrame at hframe
        rcases henter : frame.enter with result' | childEvm
        · rw [henter] at hframe
          exact ⟨result', rfl, hframe.2⟩
        · rw [henter] at hframe
          rcases hframe with ⟨raw, hnone, _⟩
          cases hnone
      rcases hdone with ⟨result', henter, hresult⟩
      subst result
      let canonical : Exec pc sevm pre out :=
        Exec.doneOk hevm henter hresume.symm next
      have hcanonical : run = canonical := Exec.unique _ _
      subst run
      rw [Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
          canonical hcommit hne]
      unfold Exec.descendantActions at hbound ⊢
      simpa only [canonical, Exec.descendantFrames, List.nil_append]
        using hbound

/-- Foreign recursive-step handler.  It reconstructs the exact retained child
and continuation, transports the installed-program fact across both edges,
accounts the child's real message entry and settlement, and then normalizes
the proof-indexed action list to `Exec.descendantFrames`. -/
theorem Exec.CoreEthSound.nextSome
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {n : Ninst}
    {cevm : Evm} {raw : Execution} {inter : Devm} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (hstep : Ninst.StepRun pc sevm pre n
      (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (hne : sevm.currentTarget ≠ ca)
    (ihChild : Exec.CoreEthSound dp ca
      cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.CoreEthSound dp ca
      (pc + n.size) sevm inter out) :
    Exec.CoreEthSound dp ca pc sevm pre out := by
  cases n with
  | reg r =>
      simp [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at hstep
  | push xs hxs =>
      simp [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at hstep
  | exec x =>
      intro run hcommit hatp _ hsum
      have hxrun := XStep.run_toStep.mp hstep
      cases hs : Xinst.step sevm pre x with
      | done ex =>
          simp [hs, XStep.Run] at hxrun
      | spawn frame resume =>
          simp only [hs, XStep.Run] at hxrun
          obtain ⟨result, hframe, hresume⟩ := hxrun
          cases result with
          | error error =>
              cases resume <;>
                simp [Resume.run, liftToExecution] at hresume
          | ok settled =>
              have henter := (RunFrame.some_inv hframe).1
              have hsettle := (RunFrame.some_inv hframe).2
              have hevm : Evm.step ⟨pc, sevm, pre⟩ =
                  .spawn frame resume (pc + 1) := by
                rw [Evm.step_next hat]
                simp only [Ninst.step_exec, hs, XStep.toStep]
              have hr : resume.run (frame.settle raw) = .ok inter := by
                rw [← hsettle]
                exact hresume.symm
              let canonical : Exec pc sevm pre out :=
                Exec.runOk hevm henter child hr next
              have hcanonical : run = canonical := Exec.unique _ _
              subst run
              obtain ⟨hpc0, hgc, hsrc⟩ :=
                Evm.step_spawn_child hevm henter
              have hchildAt : Prog.At (weth10 dp) ca
                  cevm.pc cevm.sta cevm.dyna := by
                refine ⟨?_, fun htarget => ⟨?_, hpc0⟩⟩
                · rw [hgc ca]
                  exact hatp.1
                · have hne' :
                      sevm.currentTarget ≠ cevm.sta.currentTarget := by
                    rw [htarget]
                    exact hne
                  have hcode := hsrc hne'
                    (by rw [htarget]
                        exact not_empty_of_compile hatp.1)
                    (by rw [htarget]
                        exact not_delegation_of_compile hatp.1)
                  rw [hcode, htarget]
                  exact hatp.1
              have hdirect : cevm.sta.currentTarget = ca →
                  cevm.sta.codeAddress = some ca := by
                intro htarget
                have hinnerTarget :
                    frame.inner.currentTarget = ca := by
                  rw [← Frame.enter_run_currentTarget henter]
                  exact htarget
                have hparentNe :
                    sevm.currentTarget ≠ frame.inner.currentTarget := by
                  rw [hinnerTarget]
                  exact hne
                have hnonempty :
                    pre.getCode frame.inner.currentTarget ≠ .empty := by
                  rw [hinnerTarget]
                  exact not_empty_of_compile hatp.1
                have hcadr :=
                  Xinst.step_spawn_codeAddress_eq_currentTarget
                    hs hparentNe hnonempty
                rcases Frame.enter_run_inv henter with
                  ⟨benv, htransfer, hinit⟩
                have hcadrInit :=
                  congrArg (fun e : Evm => e.sta.codeAddress) hinit
                dsimp [initEvm, initSevm, Msg.withBenv] at hcadrInit
                rw [hcadrInit, hcadr, hinnerTarget]
              have hhead := Xinst.foreignSomeEthBound
                hs hframe hresume.symm child ihChild hchildAt
                hdirect hne hsum
              have hsumInter : sum inter.state.bal < 2 ^ 256 := by
                have hnoninc := Ninst.balance_effect (.exec x)
                  ⟨.some ⟨cevm, raw⟩, ⟨child⟩, pc, hstep⟩
                exact lt_of_le_of_lt hnoninc hsum
              have hchildCode :
                  Xlot.Rel Devm.CodePreserve
                    (.some ⟨cevm, raw⟩) :=
                Exec.effect codePreserve_refl_trans.1
                  codePreserve_refl_trans.2
                  Ninst.codePreserve_effectRec
                  Jinst.codePreserve_effect
                  Linst.codePreserve_effect child
              have hcodeRel :=
                Ninst.codePreserve_effectRec (.exec x)
                  hchildCode hstep
              have hcodePreserve : Devm.CodePreserve pre inter := by
                simpa [Execution.Rel, Outcome.Rel] using hcodeRel
              have hcodeCa : inter.getCode ca = pre.getCode ca :=
                hcodePreserve ca (fun hempty =>
                  Prog.compile_ne_nil
                    (hatp.1.symm.trans (congrArg some hempty)))
              have hatpInter : Prog.At (weth10 dp) ca
                  (pc + 1) sevm inter := by
                refine ⟨?_, fun htarget => (hne htarget).elim⟩
                rw [hcodeCa]
                exact hatp.1
              have htail := ihNext next hcommit hatpInter
                (fun htarget => (hne htarget).elim) hsumInter
              have hbound := hhead.trans htail
              rw [Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
                  next hcommit hne] at hbound
              rw [Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
                  canonical hcommit hne]
              unfold Exec.descendantActions at hbound ⊢
              simp only [canonical, Exec.descendantFrames]
              by_cases hscommits :
                  Blanc.Weth10.Frame.settlementCommits frame raw = true
              · simp only [hscommits, dif_pos, if_pos,
                  List.filterMap_append, List.filterMap_cons] at hbound ⊢
                have hraw :=
                  Frame.raw_commits_of_settlementCommits hscommits
                unfold Exec.flowActions Exec.committedFrames at hbound
                simp only [dif_pos hraw, List.filterMap_cons] at hbound
                exact hbound
              · simp only [hscommits, List.filterMap_append] at hbound ⊢
                exact hbound

/-- A foreign terminal instruction closes the recursive body proof.  Failed
terminal executions cannot satisfy the committed premise; successful ones
have no descendants and are discharged by `Linst.foreignEthBound`. -/
theorem Exec.CoreEthSound.last
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst}
    {out : Execution}
    (hat : Linst.At sevm.code pc l)
    (hstep : Linst.Run sevm pre l out)
    (hne : sevm.currentTarget ≠ ca) :
    Exec.CoreEthSound dp ca pc sevm pre out := by
  intro run hcommit _ _ hsum
  have hevm : Evm.step ⟨pc, sevm, pre⟩ = .halt out := by
    rw [Evm.step_last hat]
    exact congrArg Step.halt hstep
  let canonical : Exec pc sevm pre out := Exec.halt hevm
  have hcanonical : run = canonical := Exec.unique _ _
  subst run
  cases out with
  | error e =>
      simp [Execution.commits] at hcommit
  | ok post =>
      have hbound := Linst.foreignEthBound hstep hne hsum
      rw [Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
          canonical hcommit hne]
      unfold Exec.descendantActions
      simpa only [canonical, Exec.descendantFrames, List.filterMap_nil,
        Execution.committedPost] using hbound

/-- Jump instructions are balance-silent and contribute no descendant frame;
only their concrete continuation carries actions. -/
theorem Exec.CoreEthSound.jump
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {j : Jinst}
    {pc' : Nat} {inter : Devm} {out : Execution}
    (hat : Jinst.At sevm.code pc j)
    (hstep : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out)
    (hne : sevm.currentTarget ≠ ca)
    (ih : Exec.CoreEthSound dp ca pc' sevm inter out) :
    Exec.CoreEthSound dp ca pc sevm pre out := by
  intro run hcommit hatp _ hsum
  have hevmStep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' inter := by
    rw [Evm.step_jump hat]
    exact congrArg Step.ofJump hstep
  have hcanonical : run = Exec.cont hevmStep next := Exec.unique _ _
  subst run
  have hframe := Jinst.run_instructionFrame ⟨pc, sevm, pre⟩ j
  rw [hstep] at hframe
  have hbal : inter.state.bal = pre.state.bal :=
    congrArg State.bal hframe.state.symm
  have hsumInter : sum inter.state.bal < 2 ^ 256 := by
    rw [hbal]
    exact hsum
  have hatpInter : Prog.At (weth10 dp) ca pc' sevm inter := by
    refine ⟨?_, fun htarget => (hne htarget).elim⟩
    rw [show inter.getCode ca = pre.getCode ca from
      (hframe.getCode ca).symm]
    exact hatp.1
  have hbound := ih next hcommit hatpInter
    (fun htarget => (hne htarget).elim) hsumInter
  rw [Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
      next hcommit hne] at hbound
  rw [Exec.bodyEthActions_eq_descendantActions_of_currentTarget_ne
      (Exec.cont hevmStep next) hcommit hne]
  unfold Exec.descendantActions at hbound ⊢
  simp only [Exec.descendantFrames] at hbound ⊢
  unfold EthBound at hbound ⊢
  rw [hbal] at hbound
  exact hbound

/-- The generic interpreter recursion, with every foreign/error handler
discharged.  The only input left is the exact installed WETH10 body handler at
`currentTarget = ca`. -/
theorem Exec.coreEthSound_of_compiledBodyEthHandler
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyEthHandler dp ca) :
    Exec.Fa (Exec.Wkn ca (weth10 dp)
      (fun pc sevm pre out _ =>
        Exec.CoreEthSound dp ca pc sevm pre out)) := by
  apply lift_core
    (ε := fun pc sevm pre out =>
      Exec.CoreEthSound dp ca pc sevm pre out)
    (π := fun sevm pre post =>
      Exec.CoreEthSound dp ca 0 sevm pre (.ok post))
    (analog := fun h => h)
    (ca := ca) (p := weth10 dp)
  · intro sevm pre post hrun htarget hdeeper
    exact handler hrun htarget hdeeper
  · intro pc sevm devm err devm' htarget
    exact Exec.CoreEthSound.error
  · intro pc sevm devm hnone hforeign
    exact Exec.CoreEthSound.error
  · intro pc sevm devm n err devm' hat hstep hforeign
    exact Exec.CoreEthSound.error
  · intro pc sevm devm n evm_ exn_ err devm'
      hat hstep child hforeign ihChild
    exact Exec.CoreEthSound.error
  · intro pc sevm devm n devm' exn
      hat hstep next hforeign ihNext
    exact Exec.CoreEthSound.nextNone
      hat hstep next hforeign ihNext
  · intro pc sevm devm n evm_ exn_ devm' exn
      hat hstep child next hforeign ihChild ihNext
    exact Exec.CoreEthSound.nextSome
      hat hstep child next hforeign ihChild ihNext
  · intro pc sevm devm j err devm' hat hstep hforeign
    exact Exec.CoreEthSound.error
  · intro pc sevm devm j pc' devm' exn
      hat hstep next hforeign ihNext
    exact Exec.CoreEthSound.jump
      hat hstep next hforeign ihNext
  · intro pc sevm devm l exn hat hstep hforeign
    exact Exec.CoreEthSound.last hat hstep hforeign

/-- The at-target handler discharges the public installed-body seam. -/
theorem CompiledBodyEthHandler.execBodyEthSound
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyEthHandler dp ca) :
    ExecBodyEthSound dp ca := by
  intro pc sevm pre out run hcommit hat hroot hdirect hpre
  have hfa := Exec.coreEthSound_of_compiledBodyEthHandler handler
  have hcore := hfa pc sevm pre out run hat
  exact hcore run hcommit hat
    (fun htarget => ⟨hroot, hdirect htarget⟩) hpre.side

/-- Complete committed raw-message accounting from the sole compiled handler. -/
theorem CompiledBodyEthHandler.committedExecEthSound
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyEthHandler dp ca) :
    CommittedExecEthSound dp ca :=
  ExecBodyEthSound.committedExecEthSound
    (CompiledBodyEthHandler.execBodyEthSound handler)

/-- Complete call/create/system-message accounting from the sole compiled
handler. -/
theorem CompiledBodyEthHandler.messageEthSound
    {dp : DeployParams} {ca : Adr}
    (handler : CompiledBodyEthHandler dp ca) :
    MessageEthSound dp ca :=
  CommittedExecEthSound.messageEthSound
    (CompiledBodyEthHandler.committedExecEthSound handler)

/-- Full retained Prague-history contract-ETH inequality, conditional only on
the exact installed compiled-frame handler. -/
theorem CompiledBodyEthHandler.accountedHistoryEthBound
    (chainId : UInt64) (dp : DeployParams) (ca : Adr)
    (handler : CompiledBodyEthHandler dp ca) :
    {checkpoint : BlockChain} → {future : BlockChain} →
    (history : AccountedHistory chainId dp ca checkpoint future) →
    Stable dp ca checkpoint.state →
    EthBound ca checkpoint.state future.state history.flowActions :=
  AccountedHistory.ethBound_of_committedExecSound
    chainId dp ca
      (CompiledBodyEthHandler.committedExecEthSound handler)

end Weth10

end Blanc
