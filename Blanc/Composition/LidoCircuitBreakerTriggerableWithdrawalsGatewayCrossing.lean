import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayControl
import Blanc.LidoTriggerableWithdrawalsGatewayReachability

/-!
# Parent crossings for the Triggerable Withdrawals Gateway

This composition module lifts the exact source-compiled gateway child walks through
the CircuitBreaker's `CALL` and `STATICCALL` boundaries.
-/

namespace Blanc.Composition.LidoCircuitBreakerTwg

open Jaune
open Jaune.Ninst Blanc.Ninst
open Blanc.LidoCircuitBreaker
open Blanc.LidoCircuitBreaker.PinnedTargetControl
open Blanc.LidoCircuitBreaker.PinnedTargetStubWalk
open Blanc.LidoTriggerableWithdrawalsGateway

/-! ## Parent/child boundary helpers -/

/-- The exact event emitted by a successful finite gateway pause, stated in
parent-frame vocabulary. -/
def gatewayPauseEvent (target : Adr) (duration : B256) : Log :=
  ⟨target, [signatureHash "Paused" [.uint256]], duration.toBytes⟩

/-- Exact child charge of the selected `pauseFor(uint256)` arm. -/
def gatewayPauseChildCost (duration : B256) : Nat :=
  if duration = pauseInfiniteSentinel then 29741 else 29772

private def gatewayPauseChildPost
    (sevm : Sevm) (base : Devm) (duration : B256) (G : Nat) : Devm :=
  if duration = pauseInfiniteSentinel then
    pauseSentinelPost sevm base G
  else
    pauseFinitePost sevm base duration G

/-- Exact installed width of the concrete control gateway runtime. -/
theorem controlGatewayCode_size :
    (gatewayCode controlDeployParams).size = 15948 := by
  decide +kernel

def gatewayPauseKeys (keys : Std.HashSet (Adr × B256))
    (target : Adr) (caller : B256) : Std.HashSet (Adr × B256) :=
  ((((keys.insert
    (target, roleLookupIndexSlot pauseRole caller)).insert
    (target, roleLookupRoleSlot pauseRole caller)).insert
    (target, roleLookupAccountSlot pauseRole caller)).insert
    (target, resumeSinceSlot))

theorem gatewayPauseKeys_resume_mem
    (keys : Std.HashSet (Adr × B256)) (target : Adr) (caller : B256) :
    (target, resumeSinceSlot) ∈ gatewayPauseKeys keys target caller := by
  unfold gatewayPauseKeys
  exact Std.HashSet.mem_insert_self

theorem gatewayPauseKeys_union_resume_mem
    (keys : Std.HashSet (Adr × B256)) (target : Adr) (caller : B256) :
    (target, resumeSinceSlot) ∈ keys.union
      (gatewayPauseKeys keys target caller) := by
  exact hashSetPair_mem_union_right keys (gatewayPauseKeys keys target caller)
    (target, resumeSinceSlot)
    (gatewayPauseKeys_resume_mem keys target caller)

/-- The value-zero \`CALL\` crossing whose child is the exact compiled gateway
on its cold, authorized finite \`pauseFor(uint256)\` route. -/
private lemma runCompiled_call_zero_value_gatewayPause
    {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw duration : B256} {s : List B256}
    {delegated : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨delegated, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc =
      ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_code : code = gatewayCode controlDeployParams)
    (h_mcs : gatewayPauseChildCost duration ≤ mcs)
    (h_data : ((d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).read
        iiw.toNat isw.toNat).1 =
          LidoTriggerableWithdrawalsGateway.pauseForCalldata duration)
    (h_index : d1.getStorVal cw.toAdr
      (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) = 1)
    (h_role : d1.getStorVal cw.toAdr
      (roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) = pauseRole)
    (h_account : d1.getStorVal cw.toAdr
      (roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) =
        canonicalAccount sevm.currentTarget.toB256)
    (h_coldIndex : (cw.toAdr,
      roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) ∉
        d1.accessedStorageKeys)
    (h_coldRole : (cw.toAdr,
      roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey d1 cw.toAdr
          (roleLookupIndexSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys)
    (h_coldAccount : (cw.toAdr,
      roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey d1 cw.toAdr
            (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256))
          cw.toAdr
          (roleLookupRoleSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys)
    (h_resume : d1.getStorVal cw.toAdr resumeSinceSlot = 0)
    (h_original : getOrigStorVal sevm cw.toAdr resumeSinceSlot = 0)
    (h_coldResume : (cw.toAdr, resumeSinceSlot) ∉
      (pauseRoleWarm
        { sevm with currentTarget := cw.toAdr, caller := sevm.currentTarget }
        d1).accessedStorageKeys)
    (h_dynamic : sevm.isStatic = false)
    (h_duration : duration ≠ 0)
    (_h_new : pauseForProjection sevm.benvStat.time duration ≠ 0)
    (h_time : sevm.benvStat.time <
      pauseForProjection sevm.benvStat.time duration)
    (h_room : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat [] ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) +
        (mcs - gatewayPauseChildCost duration) ∧
      post.error = devm.error ∧
      post.output = devm.output ∧
      post.returnData = [] ∧
      post.logs = devm.logs ++ [gatewayPauseEvent cw.toAdr duration] ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      post.accessedStorageKeys = devm.accessedStorageKeys.union
        (gatewayPauseKeys devm.accessedStorageKeys cw.toAdr
          sevm.currentTarget.toB256) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ d1.accessedAddresses) ∧
      post.getStorVal cw.toAdr resumeSinceSlot =
        pauseForProjection sevm.benvStat.time duration ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = (stmid.addBal cw.toAdr 0).setStorVal cw.toAdr
          resumeSinceSlot
            (pauseForProjection sevm.benvStat.time duration) := by
  let p := callSpawnParent d1 (mcc + ext)
    iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := callSpawnMsg sevm p mcs cw.toAdr dadr
    iiw.toNat isw.toNat code delegated
  have h_afford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    change ¬ (d1.getAcct sevm.currentTarget).bal < 0
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable msg rfl h_afford
  let benv' := (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  let childMsg := msg.withBenv benv'
  let childSevm := initSevm childMsg
  let childBase := initDevm childMsg
  let child := initEvm childMsg
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have hchildData : childMsg.data =
      LidoTriggerableWithdrawalsGateway.pauseForCalldata duration := by
    change (p.memory.read iiw.toNat isw.toNat).1 = _
    rw [show p.memory = d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] from
        callSpawnParent_memory]
    exact h_data
  have hsubD1 : d1.state.subBal sevm.currentTarget 0 = some stmid := by
    have hsubP : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, callSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsubP
    exact hsubP
  have hchildStor (key : B256) :
      childBase.getStorVal cw.toAdr key = d1.getStorVal cw.toAdr key := by
    change ((stmid.addBal cw.toAdr 0).get cw.toAdr).stor.get key =
      (d1.state.get cw.toAdr).stor.get key
    unfold State.addBal
    rw [State.setBal_get_stor, state_subBal_stor hsubD1]
  have hchildTarget : childSevm.currentTarget = cw.toAdr := rfl
  have hchildCaller : childSevm.caller = sevm.currentTarget := rfl
  have hchildTime : childSevm.benvStat.time = sevm.benvStat.time := rfl
  have hchildIndex : childBase.getStorVal childSevm.currentTarget
      (roleLookupIndexSlot pauseRole childSevm.caller.toB256) = 1 := by
    rw [hchildTarget, hchildCaller, hchildStor, h_index]
  have hchildRole : childBase.getStorVal childSevm.currentTarget
      (roleLookupRoleSlot pauseRole childSevm.caller.toB256) = pauseRole := by
    rw [hchildTarget, hchildCaller, hchildStor, h_role]
  have hchildAccount : childBase.getStorVal childSevm.currentTarget
      (roleLookupAccountSlot pauseRole childSevm.caller.toB256) =
        canonicalAccount childSevm.caller.toB256 := by
    rw [hchildTarget, hchildCaller, hchildStor, h_account]
  have hchildColdIndex : (childSevm.currentTarget,
      roleLookupIndexSlot pauseRole childSevm.caller.toB256) ∉
        childBase.accessedStorageKeys := by
    change (cw.toAdr,
      roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) ∉
        d1.accessedStorageKeys
    exact h_coldIndex
  have hchildColdRole : (childSevm.currentTarget,
      roleLookupRoleSlot pauseRole childSevm.caller.toB256) ∉
        (addAccessedStorageKey childBase childSevm.currentTarget
          (roleLookupIndexSlot pauseRole
            childSevm.caller.toB256)).accessedStorageKeys := by
    change (cw.toAdr,
      roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey d1 cw.toAdr
          (roleLookupIndexSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys
    exact h_coldRole
  have hchildColdAccount : (childSevm.currentTarget,
      roleLookupAccountSlot pauseRole childSevm.caller.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey childBase childSevm.currentTarget
            (roleLookupIndexSlot pauseRole childSevm.caller.toB256))
          childSevm.currentTarget
          (roleLookupRoleSlot pauseRole
            childSevm.caller.toB256)).accessedStorageKeys := by
    change (cw.toAdr,
      roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey d1 cw.toAdr
            (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256))
          cw.toAdr
          (roleLookupRoleSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys
    exact h_coldAccount
  have hchildResume :
      childBase.getStorVal childSevm.currentTarget resumeSinceSlot = 0 := by
    rw [hchildTarget, hchildStor, h_resume]
  have hchildOriginal :
      getOrigStorVal childSevm childSevm.currentTarget resumeSinceSlot = 0 := by
    change getOrigStorVal sevm cw.toAdr resumeSinceSlot = 0
    exact h_original
  have hchildColdResume : (childSevm.currentTarget, resumeSinceSlot) ∉
      (pauseRoleWarm childSevm childBase).accessedStorageKeys := by
    change (cw.toAdr, resumeSinceSlot) ∉
      (pauseRoleWarm
        { sevm with currentTarget := cw.toAdr, caller := sevm.currentTarget }
        d1).accessedStorageKeys
    exact h_coldResume
  have hcompile : some childMsg.code.toList =
      Prog.compile (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams) := by
    change some code.toList =
      Prog.compile (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
    rw [h_code]
    exact (gatewayCode_compile controlDeployParams).symm
  let exactOut := gatewayPauseChildPost childSevm childBase duration
    (mcs - gatewayPauseChildCost duration)
  have hexec : exec child = .ok exactOut := by
    by_cases hinfinite : duration = pauseInfiniteSentinel
    · subst duration
      have hmcsSentinel : 29741 ≤ mcs := by
        simpa [gatewayPauseChildCost] using h_mcs
      simpa [exactOut, gatewayPauseChildPost, gatewayPauseChildCost,
        child, childSevm, childBase] using
        pauseForSentinel_exec childMsg controlDeployParams (mcs - 29741)
          hcompile hchildData
          (by change mcs = mcs - 29741 + 29741; omega)
          rfl hchildIndex hchildRole hchildAccount hchildColdIndex
          hchildColdRole hchildColdAccount hchildResume hchildOriginal
          hchildColdResume
          (by change sevm.isStatic = false; exact h_dynamic)
    · have hfinite : duration ≠ pauseInfinitely := hinfinite
      have hmcsFinite : 29772 ≤ mcs := by
        simpa [gatewayPauseChildCost, hinfinite] using h_mcs
      have htimeFinite : sevm.benvStat.time <
          duration + sevm.benvStat.time := by
        rw [pauseForProjection, if_neg hinfinite] at h_time
        exact lt_of_lt_of_eq h_time
          (B256.add_comm (xs := sevm.benvStat.time) (ys := duration))
      simpa [exactOut, gatewayPauseChildPost, gatewayPauseChildCost,
        hinfinite, child, childSevm, childBase] using
        pauseForFinite_exec childMsg controlDeployParams duration (mcs - 29772)
          hcompile hchildData
          (by change mcs = mcs - 29772 + 29772; omega)
          rfl hchildIndex hchildRole hchildAccount hchildColdIndex
          hchildColdRole hchildColdAccount hchildResume hchildOriginal
          hchildColdResume
          (by change sevm.isStatic = false; exact h_dynamic)
          h_duration hfinite htimeFinite
  generalize houtDef : exactOut = out at hexec
  have herr : out.error = none := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split <;> simp <;> rfl
  have hout : out.output = [] := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split <;> simp <;> rfl
  have hgasOut : out.gasLeft =
      mcs - gatewayPauseChildCost duration := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split <;> simp
  have hlogsOut : out.logs = [gatewayPauseEvent cw.toAdr duration] := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split
    · rename_i hinfinite
      simp only [pauseSentinelPost_logs]
      subst duration
      rfl
    · simp only [pauseFinitePost_logs]
      rfl
  have hrefundOut : out.refundCounter = 0 := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split <;> simp only [pauseSentinelPost_refundCounter,
      pauseFinitePost_refundCounter, hchildOriginal, hchildResume]
    all_goals
      unfold sstoreNewRefundCounter
      have hrefundBase : childBase.refundCounter = 0 := rfl
      rw [hrefundBase]
      split <;> rfl
  have hatdOut : out.accountsToDelete = Std.HashSet.emptyWithCapacity := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split <;> simp <;> rfl
  have haaOut : out.accessedAddresses = p.accessedAddresses := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split <;> simp <;> rfl
  have haskOut : out.accessedStorageKeys =
      gatewayPauseKeys d1.accessedStorageKeys cw.toAdr
        sevm.currentTarget.toB256 := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split <;> simp only [pauseSentinelPost_accessedStorageKeys,
      pauseFinitePost_accessedStorageKeys] <;> rfl
  have htransOut : out.transientStorage = p.transientStorage := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split <;> simp <;> rfl
  have hstateOut : out.state =
      (stmid.addBal cw.toAdr 0).setStorVal cw.toAdr resumeSinceSlot
        (pauseForProjection sevm.benvStat.time duration) := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split
    · rename_i hinfinite
      rw [pauseSentinelPost_state, hchildTarget, pauseForProjection,
        if_pos hinfinite]
      rfl
    · rename_i hfinite
      rw [pauseFinitePost_state, hchildTarget, hchildTime,
        pauseForProjection, if_neg hfinite]
      congr 1
      exact B256.add_comm (xs := duration) (ys := sevm.benvStat.time)
  have heffectOut : out.getStorVal cw.toAdr resumeSinceSlot =
      pauseForProjection sevm.benvStat.time duration := by
    rw [← houtDef]
    simp only [exactOut, gatewayPauseChildPost]
    split
    · rename_i hinfinite
      have h := pauseSentinelPost_stored childSevm childBase
        (mcs - gatewayPauseChildCost duration)
      rw [hchildTarget] at h
      rw [h, pauseForProjection, if_pos hinfinite]
      exact pauseInfinitely_eq_shared_sentinel
    · rename_i hfinite
      have h := pauseFinitePost_stored childSevm childBase duration
        (mcs - gatewayPauseChildCost duration)
      rw [hchildTarget, hchildTime] at h
      rw [h, pauseForProjection, if_neg hfinite]
      exact B256.add_comm (xs := duration) (ys := sevm.benvStat.time)
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok out := by
    rw [hexec]
    show processMessage.settle _ (.ok out) = .ok out
    simp [processMessage.settle, herr]
  have hdi := accessDelegation_inv h_del
  have hd1stack : d1.stack = s := by
    have h := hdi.1
    change d1.stack = s at h
    exact h
  have hd1mem : d1.memory = devm.memory := by
    have h := hdi.2.1
    change d1.memory = devm.memory at h
    exact h
  have hd1frame := accessDelegation_frame h_del
  have hd1state : d1.state = devm.state := hd1frame.1
  have hd1wm := accessDelegation_worldMeta h_del
  have hd1error0 := accessDelegation_error h_del
  have hd1error : d1.error = devm.error := hd1error0
  have hd1output : d1.output = devm.output := hd1frame.2.2.2.2
  have hd1logs : d1.logs = devm.logs := hd1frame.2.1
  have hd1refund : d1.refundCounter = devm.refundCounter :=
    hd1frame.2.2.1
  have hd1delete : d1.accountsToDelete = devm.accountsToDelete :=
    hd1frame.2.2.2.1
  have hpstack : p.stack.length < 1024 := by
    change d1.stack.length < 1024
    rw [hd1stack]
    exact h_room
  let post := (((incorporateChildOnSuccess p out out.output).setMach
    ⟨1 :: p.stack, p.memory, p.gasLeft + out.gasLeft⟩).memWrite
      oiw.toNat (out.output.take osw.toNat))
  have hres : Resume.run (.call p oiw.toNat osw.toNat)
      ((Frame.ofCall msg).settle (exec child)) = .ok post := by
    rw [hsettle, Resume.run_call_ok (by rw [herr]; rfl) hpstack]
  have hrun : Ninst.RunCompiled sevm devm (.exec .call) post :=
    Ninst.runCompiled_call_zero_value h_stk h_ext h_del h_acc h_split h_gas
      h_depth (by simpa only [p, msg] using henter)
      (by simpa only [p, msg] using hres)
  refine ⟨post, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, stmid, ?_, ?_⟩
  · rw [Devm.memWrite_stack, Devm.stack_setMach]
    change 1 :: d1.stack = 1 :: s
    rw [hd1stack]
  · rw [Devm.memWrite_memory, Devm.memory_setMach, hout]
    simp only [List.take_nil]
    rw [show p.memory = d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] from
        callSpawnParent_memory]
    rw [hd1mem]
  · rw [Devm.memWrite_gasLeft, Devm.gasLeft_setMach, hgasOut]
    rw [show p.gasLeft = d1.gasLeft - (mcc + ext) from
      callSpawnParent_gasLeft]
  · change d1.error = devm.error
    exact hd1error
  · change d1.output = devm.output
    exact hd1output
  · change out.output = []
    exact hout
  · change p.logs ++ out.logs =
      devm.logs ++ [gatewayPauseEvent cw.toAdr duration]
    rw [hlogsOut, show p.logs = d1.logs from rfl, hd1logs]
  · change p.refundCounter + out.refundCounter = devm.refundCounter
    rw [hrefundOut, add_zero]
    exact hd1refund
  · change (p.accountsToDelete.union out.accountsToDelete).isEmpty =
      devm.accountsToDelete.isEmpty
    rw [hatdOut]
    rw [show p.accountsToDelete = devm.accountsToDelete from hd1delete]
    simp
  · change out.transientStorage = devm.transientStorage
    rw [htransOut]
    exact hd1wm.1
  · change p.accessedStorageKeys.union out.accessedStorageKeys = _
    rw [haskOut, show p.accessedStorageKeys = devm.accessedStorageKeys from
      hd1wm.2]
    rw [show d1.accessedStorageKeys = devm.accessedStorageKeys from hd1wm.2]
  · intro a
    change a ∈ p.accessedAddresses.union out.accessedAddresses ↔
      a ∈ d1.accessedAddresses
    rw [haaOut]
    exact ⟨fun h => (Std.HashSet.mem_union_iff.mp h).elim id id,
      fun h => Std.HashSet.mem_union_iff.mpr (Or.inl h)⟩
  · change out.getStorVal cw.toAdr resumeSinceSlot = _
    exact heffectOut
  · rw [← hd1state]
    have hsub' : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, callSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsub'
    exact hsub'
  · change out.state = _
    exact hstateOut

/-- Resolve the warm, non-delegated parent `CALL` completely.  The parent
charge is the warm access `100` plus the compiled gateway's `29772`. -/
private lemma gatewayPause_call_crossing
    {sevm : Sevm} {devm : Devm} {target iiw isw oiw osw duration : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: target :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (hgas : devm.gasLeft = G)
    (hext : devm.extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0)
    (hcode : devm.getCode target.toAdr = gatewayCode controlDeployParams)
    (hwarm : target.toAdr ∈ devm.accessedAddresses)
    (hdata : ((devm.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).read
        iiw.toNat isw.toNat).1 =
          LidoTriggerableWithdrawalsGateway.pauseForCalldata duration)
    (hindex : devm.getStorVal target.toAdr
      (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) = 1)
    (hrole : devm.getStorVal target.toAdr
      (roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) = pauseRole)
    (haccount : devm.getStorVal target.toAdr
      (roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) =
        canonicalAccount sevm.currentTarget.toB256)
    (hcoldIndex : (target.toAdr,
      roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) ∉
        devm.accessedStorageKeys)
    (hcoldRole : (target.toAdr,
      roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey devm target.toAdr
          (roleLookupIndexSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys)
    (hcoldAccount : (target.toAdr,
      roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey devm target.toAdr
            (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256))
          target.toAdr
          (roleLookupRoleSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys)
    (hresume : devm.getStorVal target.toAdr resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm target.toAdr resumeSinceSlot = 0)
    (hcoldResume : (target.toAdr, resumeSinceSlot) ∉
      (pauseRoleWarm
        { sevm with currentTarget := target.toAdr, caller := sevm.currentTarget }
        devm).accessedStorageKeys)
    (hdynamic : sevm.isStatic = false)
    (hduration : duration ≠ 0)
    (hnew : pauseForProjection sevm.benvStat.time duration ≠ 0)
    (htime : sevm.benvStat.time <
      pauseForProjection sevm.benvStat.time duration)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hfloor : gatewayPauseChildCost duration + 572 ≤ G)
    (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat [] ∧
      post.gasLeft = G - (gatewayPauseChildCost duration + 100) ∧
      post.error = devm.error ∧
      post.output = devm.output ∧
      post.returnData = [] ∧
      post.logs = devm.logs ++ [gatewayPauseEvent target.toAdr duration] ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      post.accessedStorageKeys = devm.accessedStorageKeys.union
        (gatewayPauseKeys devm.accessedStorageKeys target.toAdr
          sevm.currentTarget.toB256) ∧
      (∀ a, a ∈ post.accessedAddresses ↔
        a ∈ devm.accessedAddresses) ∧
      post.getStorVal target.toAdr resumeSinceSlot =
        pauseForProjection sevm.benvStat.time duration ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = (stmid.addBal target.toAdr 0).setStorVal target.toAdr
          resumeSinceSlot
            (pauseForProjection sevm.benvStat.time duration) := by
  have hnodel : getDelegatedCodeAddress
      ((devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr) = none := by
    rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = devm.getCode target.toAdr from rfl, hcode]
    have hsize : (gatewayCode controlDeployParams).size = 15948 := by
      exact controlGatewayCode_size
    unfold getDelegatedCodeAddress
    rw [if_neg]
    intro hvalid
    have hs := hvalid.1
    rw [hsize] at hs
    norm_num [eoaDelegatedCodeLength] at hs
  have hdel : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        target.toAdr) target.toAdr =
      ⟨false, target.toAdr,
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
          target.toAdr, 0,
        addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
          target.toAdr⟩ := by
    unfold accessDelegation
    simp only [show (addAccessedAddress
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        target.toAdr).state.getCode target.toAdr =
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr from rfl, hnodel]
  set d0 := addAccessedAddress
    (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) target.toAdr with hd0
  have hd0gas : d0.gasLeft = G := by
    rw [show d0.gasLeft = devm.gasLeft from rfl, hgas]
  have hacc : accessCost target.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses + 0 =
      gasWarmAccess := by
    show accessCost target.toAdr devm.accessedAddresses + 0 = gasWarmAccess
    unfold accessCost
    rw [if_pos hwarm]
    omega
  obtain ⟨mcc, mcs, hsplit⟩ : ∃ mcc mcs,
      calculateMsgCallGas 0 (Nat.toB256 G).toNat d0.gasLeft 0
        gasWarmAccess = ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs, hcross, hgasout⟩ :
      gatewayPauseChildCost duration ≤ mcs ∧ mcc + 0 ≤ G ∧
        G - (mcc + 0) + (mcs - gatewayPauseChildCost duration) =
          G - (gatewayPauseChildCost duration + 100) := by
    have hGnat : (Nat.toB256 G).toNat = G :=
      B256.toNat_toB256_of_lt hbound
    rw [hd0gas] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, if_neg (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin : min G (except64th (G - 0 - 100)) =
        except64th (G - 100) := by
      have h1 : except64th (G - 0 - 100) ≤ G := by
        unfold except64th
        omega
      rw [Nat.min_eq_right h1]
      norm_num
    rw [hmin] at hsplit
    have h1 : except64th (G - 100) + 100 = mcc :=
      congrArg Prod.fst hsplit
    have h2 : except64th (G - 100) + 0 = mcs :=
      congrArg Prod.snd hsplit
    unfold except64th at h1 h2
    by_cases hinfinite : duration = pauseInfiniteSentinel
    · simp [gatewayPauseChildCost, hinfinite] at hfloor ⊢
      exact ⟨by omega, by omega, by omega⟩
    · simp [gatewayPauseChildCost, hinfinite] at hfloor ⊢
      exact ⟨by omega, by omega, by omega⟩
  have hd0mem : d0.memory = devm.memory := rfl
  have hd0index : d0.getStorVal target.toAdr
      (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) = 1 := hindex
  have hd0role : d0.getStorVal target.toAdr
      (roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) = pauseRole := hrole
  have hd0account : d0.getStorVal target.toAdr
      (roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) =
        canonicalAccount sevm.currentTarget.toB256 := haccount
  have hd0coldIndex : (target.toAdr,
      roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) ∉
        d0.accessedStorageKeys := hcoldIndex
  have hd0coldRole : (target.toAdr,
      roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey d0 target.toAdr
          (roleLookupIndexSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys := hcoldRole
  have hd0coldAccount : (target.toAdr,
      roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey d0 target.toAdr
            (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256))
          target.toAdr
          (roleLookupRoleSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys := hcoldAccount
  have hd0resume : d0.getStorVal target.toAdr resumeSinceSlot = 0 := hresume
  have hd0coldResume : (target.toAdr, resumeSinceSlot) ∉
      (pauseRoleWarm
        { sevm with currentTarget := target.toAdr, caller := sevm.currentTarget }
        d0).accessedStorageKeys := hcoldResume
  obtain ⟨post, hrun, hstack, hmem, hgasl, herr, hout, hret, hlogs,
    hrefund, hatd, htrans, hask, haa, heffect, stmid, hsub, hstate⟩ :=
    runCompiled_call_zero_value_gatewayPause
      (gw := Nat.toB256 G) (cw := target) (duration := duration)
      hstk
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0 from hext)
      hdel hacc hsplit (by rw [hd0gas]; exact hcross) hdepth hnp
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = gatewayCode controlDeployParams from hcode)
      hmcs (by simpa only [hd0mem] using hdata) hd0index hd0role hd0account
      hd0coldIndex hd0coldRole hd0coldAccount hd0resume horiginal
      hd0coldResume hdynamic hduration hnew htime hroom
  refine ⟨post, hrun, hstack, hmem, ?_, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, ?_, heffect, stmid, hsub, hstate⟩
  · rw [hgasl, hd0gas]
    exact hgasout
  · intro a
    rw [haa a]
    show a ∈ devm.accessedAddresses.insert target.toAdr ↔
      a ∈ devm.accessedAddresses
    constructor
    · intro hx
      rcases Std.HashSet.mem_insert.mp hx with he | hx'
      · exact (eq_of_beq he) ▸ hwarm
      · exact hx'
    · intro hx
      exact Std.HashSet.mem_insert.mpr (Or.inr hx)

/-- The `STATICCALL` crossing whose child is the source-compiled gateway on its
warm canonical-true query route. -/
private lemma runCompiled_statcall_gatewayQuery
    {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw storedUntil : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc =
      ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_code : code = gatewayCode controlDeployParams)
    (h_mcs : 220 ≤ mcs)
    (h_data : ((d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).read
        iiw.toNat isw.toNat).1 =
          LidoTriggerableWithdrawalsGateway.isPausedCalldata)
    (h_stored : d1.getStorVal tw.toAdr resumeSinceSlot = storedUntil)
    (h_warm : (tw.toAdr, resumeSinceSlot) ∈ d1.accessedStorageKeys)
    (h_paused : sevm.benvStat.time < storedUntil)
    (h_room : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .staticcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) + (mcs - 220) ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ d1.accessedAddresses) ∧
      post.getStorVal tw.toAdr resumeSinceSlot = storedUntil ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal tw.toAdr 0 := by
  let p := callSpawnParent d1 (mcc + ext)
    iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := staticcallSpawnMsg sevm p mcs tw.toAdr dadr
    iiw.toNat isw.toNat code dp
  have h_afford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    change ¬ (d1.getAcct sevm.currentTarget).bal < 0
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable msg rfl h_afford
  let benv' := (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  let childMsg := msg.withBenv benv'
  let child := initEvm childMsg
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have hchildData : childMsg.data =
      LidoTriggerableWithdrawalsGateway.isPausedCalldata := by
    change (p.memory.read iiw.toNat isw.toNat).1 = _
    rw [show p.memory = d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] from
        callSpawnParent_memory]
    exact h_data
  have hsubD1 : d1.state.subBal sevm.currentTarget 0 = some stmid := by
    have hsubP : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, staticcallSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsubP
    exact hsubP
  have hchildStored :
      (initDevm childMsg).getStorVal tw.toAdr resumeSinceSlot =
        storedUntil := by
    change ((stmid.addBal tw.toAdr 0).get tw.toAdr).stor.get
      resumeSinceSlot = storedUntil
    unfold State.addBal
    rw [State.setBal_get_stor, state_subBal_stor hsubD1]
    exact h_stored
  have hchildWarm :
      (tw.toAdr, resumeSinceSlot) ∈
        (initDevm childMsg).accessedStorageKeys := by
    change (tw.toAdr, resumeSinceSlot) ∈ p.accessedStorageKeys
    change (tw.toAdr, resumeSinceSlot) ∈ d1.accessedStorageKeys
    exact h_warm
  have hcompile : some childMsg.code.toList =
      Prog.compile (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams) := by
    change some code.toList =
      Prog.compile (LidoTriggerableWithdrawalsGateway.runtime controlDeployParams)
    rw [h_code]
    exact (gatewayCode_compile controlDeployParams).symm
  obtain ⟨out, hexec, hout, heffectOut, hgasOut, herr, hmetaOut,
    hworldOut⟩ :=
    isPaused_true_warm_exec childMsg controlDeployParams storedUntil (mcs - 220)
      hcompile hchildData
      (by change mcs = mcs - 220 + 220; omega)
      rfl hchildStored hchildWarm
      (by change sevm.benvStat.time < storedUntil; exact h_paused)
  have hlogsOut : out.logs = [] := by
    rw [show out.logs =
      ((initDevm childMsg).withOutput
        (1 : B256).toBytes).logs from
      congrArg (fun view => view.logs) hmetaOut]
    rfl
  have hrefundOut : out.refundCounter = 0 := by
    rw [show out.refundCounter =
      ((initDevm childMsg).withOutput
        (1 : B256).toBytes).refundCounter from
      congrArg (fun view => view.refundCounter) hmetaOut]
    rfl
  have hatdOut : out.accountsToDelete = Std.HashSet.emptyWithCapacity := by
    rw [show out.accountsToDelete =
      ((initDevm childMsg).withOutput
        (1 : B256).toBytes).accountsToDelete from
      congrArg (fun view => view.accountsToDelete) hmetaOut]
    rfl
  have haaOut : out.accessedAddresses = p.accessedAddresses := by
    rw [show out.accessedAddresses =
      ((initDevm childMsg).withOutput
        (1 : B256).toBytes).accessedAddresses from
      congrArg (fun view => view.accessedAddresses) hmetaOut]
    rfl
  have haskOut : out.accessedStorageKeys = p.accessedStorageKeys := by
    rw [show out.accessedStorageKeys =
      ((initDevm childMsg).withOutput
        (1 : B256).toBytes).accessedStorageKeys from
      congrArg (fun view => view.accessedStorageKeys) hmetaOut]
    rfl
  have htransOut : out.transientStorage = p.transientStorage := by
    rw [show out.transientStorage =
      (initDevm childMsg).transientStorage from
      congrArg (fun world => world.transientStorage) hworldOut]
    rfl
  have hstateOut : out.state = stmid.addBal tw.toAdr 0 := by
    rw [show out.state = (initDevm childMsg).state from
      congrArg (fun world => world.state) hworldOut]
    rfl
  have herr0 : out.error = none := by
    rw [herr]
    rfl
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok out := by
    rw [show exec child = .ok out from hexec]
    show processMessage.settle _ (.ok out) = .ok out
    simp [processMessage.settle, herr0]
  have hdi := accessDelegation_inv h_del
  have hd1stack : d1.stack = s := by
    have h := hdi.1
    change d1.stack = s at h
    exact h
  have hd1mem : d1.memory = devm.memory := by
    have h := hdi.2.1
    change d1.memory = devm.memory at h
    exact h
  have hd1frame := accessDelegation_frame h_del
  have hd1wm := accessDelegation_worldMeta h_del
  have hd1error0 := accessDelegation_error h_del
  have hd1error : d1.error = devm.error := hd1error0
  have hd1state : d1.state = devm.state := hd1frame.1
  have hd1logs : d1.logs = devm.logs := hd1frame.2.1
  have hd1refund : d1.refundCounter = devm.refundCounter :=
    hd1frame.2.2.1
  have hd1delete : d1.accountsToDelete = devm.accountsToDelete :=
    hd1frame.2.2.2.1
  have hd1output : d1.output = devm.output := hd1frame.2.2.2.2
  have hpstack : p.stack.length < 1024 := by
    change d1.stack.length < 1024
    rw [hd1stack]
    exact h_room
  let post := (((incorporateChildOnSuccess p out out.output).setMach
    ⟨1 :: p.stack, p.memory, p.gasLeft + out.gasLeft⟩).memWrite
      oiw.toNat (out.output.take osw.toNat))
  have hres : Resume.run (.call p oiw.toNat osw.toNat)
      ((Frame.ofCall msg).settle (exec child)) = .ok post := by
    rw [hsettle, Resume.run_call_ok (by rw [herr]; rfl) hpstack]
  have hrun : Ninst.RunCompiled sevm devm (.exec .staticcall) post :=
    Ninst.runCompiled_exec_run
      (Xinst.step_staticcall_spawn h_stk h_ext h_del h_acc h_split h_gas
        h_depth)
      (by simpa only [p, msg] using henter)
      (by simpa only [p, msg] using hres)
  refine ⟨post, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, stmid, ?_, ?_⟩
  · rw [Devm.memWrite_stack, Devm.stack_setMach]
    change 1 :: d1.stack = 1 :: s
    rw [hd1stack]
  · rw [Devm.memWrite_memory, Devm.memory_setMach, hout]
    rw [show p.memory = d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] from
        callSpawnParent_memory]
    rw [hd1mem]
  · rw [Devm.memWrite_gasLeft, Devm.gasLeft_setMach, hgasOut]
    rw [show p.gasLeft = d1.gasLeft - (mcc + ext) from
      callSpawnParent_gasLeft]
  · change d1.error = devm.error
    exact hd1error
  · change d1.output = devm.output
    exact hd1output
  · change out.output = (1 : B256).toBytes
    exact hout
  · change p.logs ++ out.logs = devm.logs
    rw [hlogsOut, List.append_nil]
    exact hd1logs
  · change p.refundCounter + out.refundCounter = devm.refundCounter
    rw [hrefundOut, add_zero]
    exact hd1refund
  · change (p.accountsToDelete.union out.accountsToDelete).isEmpty =
      devm.accountsToDelete.isEmpty
    rw [hatdOut]
    rw [show p.accountsToDelete = devm.accountsToDelete from hd1delete]
    simp
  · change out.transientStorage = devm.transientStorage
    rw [htransOut]
    exact hd1wm.1
  · intro k
    change k ∈ p.accessedStorageKeys.union out.accessedStorageKeys ↔
      k ∈ devm.accessedStorageKeys
    rw [haskOut, show p.accessedStorageKeys = devm.accessedStorageKeys from
      hd1wm.2]
    exact ⟨fun h => (Std.HashSet.mem_union_iff.mp h).elim id id,
      fun h => Std.HashSet.mem_union_iff.mpr (Or.inl h)⟩
  · intro a
    change a ∈ p.accessedAddresses.union out.accessedAddresses ↔
      a ∈ d1.accessedAddresses
    rw [haaOut]
    exact ⟨fun h => (Std.HashSet.mem_union_iff.mp h).elim id id,
      fun h => Std.HashSet.mem_union_iff.mpr (Or.inl h)⟩
  · change out.getStorVal tw.toAdr resumeSinceSlot = storedUntil
    exact heffectOut
  · rw [← hd1state]
    have hsub' : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, staticcallSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsub'
    exact hsub'
  · change out.state = stmid.addBal tw.toAdr 0
    exact hstateOut

/-- Resolve the warm, non-delegated parent `STATICCALL` completely.  The
parent charge is the warm access `100` plus the compiled gateway's `220`. -/
private lemma gatewayQuery_statcall_crossing
    {sevm : Sevm} {devm : Devm} {target iiw isw oiw osw storedUntil : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: target :: iiw :: isw :: oiw :: osw :: s)
    (hgas : devm.gasLeft = G)
    (hext : devm.extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0)
    (hcode : devm.getCode target.toAdr = gatewayCode controlDeployParams)
    (hwarm : target.toAdr ∈ devm.accessedAddresses)
    (hdata : ((devm.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).read
        iiw.toNat isw.toNat).1 =
          LidoTriggerableWithdrawalsGateway.isPausedCalldata)
    (hstored : devm.getStorVal target.toAdr resumeSinceSlot = storedUntil)
    (hwarmSlot : (target.toAdr, resumeSinceSlot) ∈
      devm.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hfloor : 323 ≤ G) (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .staticcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = G - 320 ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ devm.accessedAddresses) ∧
      post.getStorVal target.toAdr resumeSinceSlot = storedUntil ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal target.toAdr 0 := by
  have hnodel : getDelegatedCodeAddress
      ((devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr) = none := by
    rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = devm.getCode target.toAdr from rfl, hcode]
    have hsize : (gatewayCode controlDeployParams).size = 15948 := by
      exact controlGatewayCode_size
    unfold getDelegatedCodeAddress
    rw [if_neg]
    intro hvalid
    have hs := hvalid.1
    rw [hsize] at hs
    norm_num [eoaDelegatedCodeLength] at hs
  have hdel : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        target.toAdr) target.toAdr =
      ⟨false, target.toAdr,
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
          target.toAdr, 0,
        addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
          target.toAdr⟩ := by
    unfold accessDelegation
    simp only [show (addAccessedAddress
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        target.toAdr).state.getCode target.toAdr =
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr from rfl, hnodel]
  set d0 := addAccessedAddress
    (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) target.toAdr with hd0
  have hd0gas : d0.gasLeft = G := by
    rw [show d0.gasLeft = devm.gasLeft from rfl, hgas]
  have hacc : accessCost target.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses + 0 =
      gasWarmAccess := by
    show accessCost target.toAdr devm.accessedAddresses + 0 = gasWarmAccess
    unfold accessCost
    rw [if_pos hwarm]
    omega
  obtain ⟨mcc, mcs, hsplit⟩ : ∃ mcc mcs,
      calculateMsgCallGas 0 (Nat.toB256 G).toNat d0.gasLeft 0
        gasWarmAccess = ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs, hcross, hgasout⟩ :
      220 ≤ mcs ∧ mcc + 0 ≤ G ∧
        G - (mcc + 0) + (mcs - 220) = G - 320 := by
    have hGnat : (Nat.toB256 G).toNat = G :=
      B256.toNat_toB256_of_lt hbound
    rw [hd0gas] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, if_neg (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin : min G (except64th (G - 0 - 100)) =
        except64th (G - 100) := by
      have h1 : except64th (G - 0 - 100) ≤ G := by
        unfold except64th
        omega
      rw [Nat.min_eq_right h1]
      norm_num
    rw [hmin] at hsplit
    have h1 : except64th (G - 100) + 100 = mcc :=
      congrArg Prod.fst hsplit
    have h2 : except64th (G - 100) + 0 = mcs :=
      congrArg Prod.snd hsplit
    unfold except64th at h1 h2
    exact ⟨by omega, by omega, by omega⟩
  have hd0mem : d0.memory = devm.memory := rfl
  have hd0stored : d0.getStorVal target.toAdr resumeSinceSlot =
      storedUntil := by exact hstored
  have hd0warmSlot : (target.toAdr, resumeSinceSlot) ∈
      d0.accessedStorageKeys := by exact hwarmSlot
  obtain ⟨post, hrun, hstack, hmem, hgasl, herr, hout, hret, hlogs,
    hrefund, hatd, htrans, hask, haa, heffect, stmid, hsub, hstate⟩ :=
    runCompiled_statcall_gatewayQuery
      (gw := Nat.toB256 G) (tw := target) (storedUntil := storedUntil)
      hstk
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0 from hext)
      hdel hacc hsplit (by rw [hd0gas]; exact hcross) hdepth hnp
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = gatewayCode controlDeployParams from hcode)
      hmcs (by simpa only [hd0mem] using hdata) hd0stored hd0warmSlot
      hpaused hroom
  refine ⟨post, hrun, hstack, hmem, ?_, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, ?_, heffect, stmid, hsub, hstate⟩
  · rw [hgasl, hd0gas]
    exact hgasout
  · intro a
    rw [haa a]
    show a ∈ devm.accessedAddresses.insert target.toAdr ↔
      a ∈ devm.accessedAddresses
    constructor
    · intro hx
      rcases Std.HashSet.mem_insert.mp hx with he | hx'
      · exact (eq_of_beq he) ▸ hwarm
      · exact hx'
    · intro hx
      exact Std.HashSet.mem_insert.mpr (Or.inr hx)


private theorem installedCodeGuard_runCompiled
    (fs : List Func) (sevm : Sevm) (devm : Devm)
    (codeSize target : B256) (M : Mem) (G : Nat)
    (tail : Func) (post : Devm)
    (hcodeSize : codeSize ≠ 0)
    (htail : Func.RunCompiled fs sevm
      (devm.setMach ⟨[], M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (devm.setMach ⟨[codeSize, target], M, G + 18⟩)
      (Ninst.iszero :::
        ((Func.call emptyRevertSlot) <?> (Ninst.pop ::: tail))) post := by
  func_run (3) [0]
  case h_val => simp [B256.eqCheck, hcodeSize]
  case a =>
    have hg : G + 18 - 18 = G := by omega
    rw [hg]
    exact htail

/-- The complete `pauseAfterSet` suffix when both external boundaries execute
the installed source-compiled Triggerable Withdrawals Gateway. -/
theorem pauseAfterSet_gateway_toSuccess_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (target duration : B256) (M : Mem) (img : Bytes)
    (codeCost Gb : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hduration : Bytes.toB256
      (img.sliceD (durationWord * 32).toNat 32 0) = duration)
    (hsize : M.size = 768)
    (hcodeCost : temporalAccountAccessCost base target.toAdr = codeCost)
    (hgatewayCode : base.getCode target.toAdr = gatewayCode controlDeployParams)
    (hindex : base.getStorVal target.toAdr
      (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) = 1)
    (hrole : base.getStorVal target.toAdr
      (roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) = pauseRole)
    (haccount : base.getStorVal target.toAdr
      (roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) =
        canonicalAccount sevm.currentTarget.toB256)
    (hcoldIndex : (target.toAdr,
      roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) ∉
        base.accessedStorageKeys)
    (hcoldRole : (target.toAdr,
      roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey base target.toAdr
          (roleLookupIndexSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys)
    (hcoldAccount : (target.toAdr,
      roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) ∉
        (addAccessedStorageKey
          (addAccessedStorageKey base target.toAdr
            (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256))
          target.toAdr
          (roleLookupRoleSlot pauseRole
            sevm.currentTarget.toB256)).accessedStorageKeys)
    (hresume : base.getStorVal target.toAdr resumeSinceSlot = 0)
    (horiginal : getOrigStorVal sevm target.toAdr resumeSinceSlot = 0)
    (hcoldResume : (target.toAdr, resumeSinceSlot) ∉
      (pauseRoleWarm
        { sevm with currentTarget := target.toAdr, caller := sevm.currentTarget }
        base).accessedStorageKeys)
    (hdynamic : sevm.isStatic = false)
    (hdurationNonzero : duration ≠ 0)
    (hnew : pauseForProjection sevm.benvStat.time duration ≠ 0)
    (hpaused : sevm.benvStat.time <
      pauseForProjection sevm.benvStat.time duration)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hgasfloor : 46 ≤ Gb)
    (hbound : Gb + gatewayPauseChildCost duration + 526 < 2 ^ 256) :
    ∃ mid : Devm,
      mid.stack = [] ∧
      mid.memory = pauseDecodedMemory M duration ∧
      mid.gasLeft = Gb - 19 ∧
      mid.error = base.error ∧
      mid.output = base.output ∧
      mid.returnData = (1 : B256).toBytes ∧
      mid.logs = base.logs ++ [gatewayPauseEvent target.toAdr duration] ∧
      mid.refundCounter = base.refundCounter ∧
      mid.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty ∧
      mid.transientStorage = base.transientStorage ∧
      (∀ k, k ∈ mid.accessedStorageKeys ↔
        k ∈ base.accessedStorageKeys.union
          (gatewayPauseKeys base.accessedStorageKeys target.toAdr
            sevm.currentTarget.toB256)) ∧
      (∀ a, a ∈ mid.accessedAddresses ↔
        (a = target.toAdr ∨ a ∈ base.accessedAddresses)) ∧
      mid.getStorVal target.toAdr resumeSinceSlot =
        pauseForProjection sevm.benvStat.time duration ∧
      (∃ st₁ st₂ : State,
        base.state.subBal sevm.currentTarget 0 = some st₁ ∧
        ((st₁.addBal target.toAdr 0).setStorVal target.toAdr
          resumeSinceSlot
            (pauseForProjection sevm.benvStat.time duration)).subBal
            sevm.currentTarget 0 = some st₂ ∧
        mid.state = st₂.addBal target.toAdr 0) ∧
      ∀ post : Devm,
        Func.RunCompiled fs sevm mid pauseSuccess post →
        Func.RunCompiled fs sevm
          (base.setMach ⟨[], M,
            Gb + gatewayPauseChildCost duration + 594 + codeCost⟩)
          pauseAfterSet post := by
  have halign : M.size % 32 = 0 := by omega
  have hwf1 : Mem.Wf (M.write 256 pauseForSelector.toBytes) :=
    hwf.write _ _
  have hwf2 : Mem.Wf ((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes) := hwf1.write _ _
  have hsize1 : (M.write 256 pauseForSelector.toBytes).size = 768 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)]
    exact hsize
  have hsize2 : ((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).size = 768 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)]
    exact hsize1
  have hsize3 : (((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).write 256 isPausedSelector.toBytes).size = 768 := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)]
    exact hsize2
  have halign2 : ((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).size % 32 = 0 := by omega
  have halign3 : (((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).write 256 isPausedSelector.toBytes).size % 32 = 0 := by
    omega
  have htargetMemory0 : (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have htargetValue0 :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads]
    exact htarget
  have hreads1 : Mem.Reads (M.write 256 pauseForSelector.toBytes)
      (Bytes.writeAt img 256 pauseForSelector.toBytes) :=
    Mem.Reads.write hwf hreads 256 _
  have hdurationMemory1 :
      ((M.write 256 pauseForSelector.toBytes).read
        (durationWord * 32).toNat 32).2 =
      M.write 256 pauseForSelector.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le (by omega) (by
      have hoff : (durationWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have hdurationValue1 :
      ((M.write 256 pauseForSelector.toBytes).read
        (durationWord * 32).toNat 32).1.toB256 = duration := by
    rw [Mem.Reads.read hreads1]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact hduration
  have hreads2 : Mem.Reads
      ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
      (Bytes.writeAt (Bytes.writeAt img 256 pauseForSelector.toBytes) 288
        duration.toBytes) :=
    Mem.Reads.write hwf1 hreads1 288 _
  have hpauseWindow :
      (((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).read 284 36).1 =
          LidoTriggerableWithdrawalsGateway.pauseForCalldata duration := by
    rw [Mem.Reads.read hreads2]
    rw [pauseForCalldata_eq]
    exact Blanc.LidoCircuitBreaker.sliceD_stagedCalldata
      img pauseForSelector duration
  have htargetMemory2 :
      (((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).read (targetWord * 32).toNat 32).2 =
      (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign2 (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have htargetValue2 :
      (((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).read (targetWord * 32).toNat 32).1.toB256 =
      target := by
    rw [Mem.Reads.read hreads2]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact htarget
  have hreads3 : Mem.Reads (((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).write 256 isPausedSelector.toBytes)
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 256
        pauseForSelector.toBytes) 288 duration.toBytes) 256
        isPausedSelector.toBytes) :=
    Mem.Reads.write hwf2 hreads2 256 _
  have hqueryWindow :
      ((((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).write 256 isPausedSelector.toBytes).read
          284 4).1 = LidoTriggerableWithdrawalsGateway.isPausedCalldata := by
    rw [Mem.Reads.read hreads3]
    rw [isPausedCalldata_eq]
    exact Blanc.LidoCircuitBreaker.sliceD_stagedSelector
      (Bytes.writeAt (Bytes.writeAt img 256 pauseForSelector.toBytes)
        288 duration.toBytes) isPausedSelector
  have htargetMemory3 :
      ((((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).write 256 isPausedSelector.toBytes).read
          (targetWord * 32).toNat 32).2 =
      ((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).write 256 isPausedSelector.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign3 (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have htargetValue3 :
      ((((M.write 256 pauseForSelector.toBytes).write 288
        duration.toBytes).write 256 isPausedSelector.toBytes).read
          (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads3]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact htarget
  have honeBytes : (1 : B256).toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes (1 : B256)
    rw [h] at hlen
    simp at hlen
  have hdecodedValue :
      ((pauseDecodedMemory M duration).read 0 32).1.toB256 = 1 := by
    rw [pauseDecodedMemory, show (32 : Nat) =
      (1 : B256).toBytes.length from (B256.length_toBytes 1).symm,
      Mem.read_write_zero _ honeBytes, B256.toB256_toBytes]
  have hsize4 : (pauseDecodedMemory M duration).size = 768 := by
    rw [pauseDecodedMemory, pauseStagedMemory,
      Mem.size_write_of_le (by rw [B256.length_toBytes]; omega)]
    exact hsize3
  have hdecodedMemory :
      ((pauseDecodedMemory M duration).read 0 32).2 =
        pauseDecodedMemory M duration := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le (by omega) (by omega))]
  have hgatewaySize :
      (gatewayCode controlDeployParams).size.toB256 = (15948 : B256) := by
    rw [controlGatewayCode_size]
    decide +kernel
  obtain ⟨post1, hrun1, hstk1, hmem1, hgas1, herr1, hout1, hret1, hlogs1,
    hrefund1, hatd1, htrans1, hask1, haa1, heffect1, st₁, hsub1,
    hstate1⟩ :=
    gatewayPause_call_crossing (sevm := sevm)
      (devm := (temporalAccountAccessBase base target.toAdr).setMach
        ⟨[Nat.toB256 (Gb + gatewayPauseChildCost duration + 526),
            target, 0, 284, 36, 0, 0],
          (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
          Gb + gatewayPauseChildCost duration + 526⟩)
      (target := target) (iiw := 284) (isw := 36) (oiw := 0) (osw := 0)
      (duration := duration) (s := [])
      (G := Gb + gatewayPauseChildCost duration + 526)
      rfl rfl
      (by
        show ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[Nat.toB256 (Gb + gatewayPauseChildCost duration + 526),
              target, 0, 284, 36, 0, 0],
            (M.write 256 pauseForSelector.toBytes).write 288
              duration.toBytes,
            Gb + gatewayPauseChildCost duration + 526⟩).extCost _ = 0
        exact Devm.extCost_covered (by rw [hsize2]; decide))
      (by
        show (temporalAccountAccessBase base target.toAdr).getCode
          target.toAdr = gatewayCode controlDeployParams
        rw [temporalAccountAccessBase_getCode]
        exact hgatewayCode)
      (temporalAccountAccessBase_warm base target.toAdr)
      (by
        simp only [Devm.memory_setMach]
        rw [Mem.extends_covered (by rw [hsize2]; decide)]
        exact hpauseWindow)
      (by
        show (temporalAccountAccessBase base target.toAdr).getStorVal
          target.toAdr
            (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) = 1
        simpa only [Devm.getStorVal, Devm.getAcct,
          temporalAccountAccessBase_state] using hindex)
      (by
        show (temporalAccountAccessBase base target.toAdr).getStorVal
          target.toAdr
            (roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) =
              pauseRole
        simpa only [Devm.getStorVal, Devm.getAcct,
          temporalAccountAccessBase_state] using hrole)
      (by
        show (temporalAccountAccessBase base target.toAdr).getStorVal
          target.toAdr
            (roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) =
              canonicalAccount sevm.currentTarget.toB256
        simpa only [Devm.getStorVal, Devm.getAcct,
          temporalAccountAccessBase_state] using haccount)
      (by
        change (target.toAdr,
          roleLookupIndexSlot pauseRole sevm.currentTarget.toB256) ∉
            (temporalAccountAccessBase base target.toAdr).accessedStorageKeys
        rw [temporalAccountAccessBase_accessedStorageKeys]
        exact hcoldIndex)
      (by
        change (target.toAdr,
          roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) ∉
            (addAccessedStorageKey
              (temporalAccountAccessBase base target.toAdr) target.toAdr
              (roleLookupIndexSlot pauseRole
                sevm.currentTarget.toB256)).accessedStorageKeys
        change (target.toAdr,
          roleLookupRoleSlot pauseRole sevm.currentTarget.toB256) ∉
            (temporalAccountAccessBase base target.toAdr).accessedStorageKeys.insert
              (target.toAdr,
                roleLookupIndexSlot pauseRole sevm.currentTarget.toB256)
        rw [temporalAccountAccessBase_accessedStorageKeys]
        exact hcoldRole)
      (by
        change (target.toAdr,
          roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) ∉
            (addAccessedStorageKey
              (addAccessedStorageKey
                (temporalAccountAccessBase base target.toAdr) target.toAdr
                (roleLookupIndexSlot pauseRole sevm.currentTarget.toB256))
              target.toAdr
              (roleLookupRoleSlot pauseRole
                sevm.currentTarget.toB256)).accessedStorageKeys
        change (target.toAdr,
          roleLookupAccountSlot pauseRole sevm.currentTarget.toB256) ∉
            ((temporalAccountAccessBase base target.toAdr).accessedStorageKeys.insert
              (target.toAdr,
                roleLookupIndexSlot pauseRole sevm.currentTarget.toB256)).insert
              (target.toAdr,
                roleLookupRoleSlot pauseRole sevm.currentTarget.toB256)
        rw [temporalAccountAccessBase_accessedStorageKeys]
        exact hcoldAccount)
      (by
        show (temporalAccountAccessBase base target.toAdr).getStorVal
          target.toAdr resumeSinceSlot = 0
        simpa only [Devm.getStorVal, Devm.getAcct,
          temporalAccountAccessBase_state] using hresume)
      horiginal
      (by
        change (target.toAdr, resumeSinceSlot) ∉
          (((temporalAccountAccessBase base target.toAdr).accessedStorageKeys.insert
            (target.toAdr,
              roleLookupIndexSlot pauseRole sevm.currentTarget.toB256)).insert
            (target.toAdr,
              roleLookupRoleSlot pauseRole sevm.currentTarget.toB256)).insert
            (target.toAdr,
              roleLookupAccountSlot pauseRole sevm.currentTarget.toB256)
        rw [temporalAccountAccessBase_accessedStorageKeys]
        exact hcoldResume)
      hdynamic hdurationNonzero hnew hpaused hdepth hnp
      (by omega) hbound (by simp)
  have hgas1' : post1.gasLeft = Gb + 426 := by
    rw [hgas1]
    omega
  have hmem1' : post1.memory =
      (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes := by
    simp only [Devm.memory_setMach] at hmem1
    rw [hmem1,
      show ((0 : B256)).toNat = 0 by decide,
      Mem.extends_covered (by rw [hsize2]; decide)]
    rfl
  have heta1 : post1 = post1.setMach ⟨[1],
      (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
      Gb + 426⟩ := by
    rw [← hstk1, ← hmem1', ← hgas1']
    rfl
  have hcode1 : post1.state.getCode target.toAdr = gatewayCode controlDeployParams := by
    have hwriteCode :
        ((st₁.addBal target.toAdr 0).setStorVal target.toAdr
          resumeSinceSlot
            (pauseForProjection sevm.benvStat.time duration)).getCode
            target.toAdr =
          (st₁.addBal target.toAdr 0).getCode target.toAdr := by
      unfold State.getCode
      have h := congrFun
        (State.setStorVal_balCodeEq (st₁.addBal target.toAdr 0)
          target.toAdr resumeSinceSlot
            (pauseForProjection sevm.benvStat.time duration))
        target.toAdr
      exact (congrArg Prod.snd h).symm
    rw [hstate1, hwriteCode, State.addBal_getCode,
      State.subBal_getCode hsub1]
    show (temporalAccountAccessBase base target.toAdr).state.getCode
      target.toAdr = gatewayCode controlDeployParams
    rw [temporalAccountAccessBase_state]
    exact hgatewayCode
  have hask1' : post1.accessedStorageKeys =
      base.accessedStorageKeys.union
        (gatewayPauseKeys base.accessedStorageKeys target.toAdr
          sevm.currentTarget.toB256) := by
    rw [hask1]
    change (temporalAccountAccessBase base target.toAdr
      ).accessedStorageKeys.union
        (gatewayPauseKeys
          (temporalAccountAccessBase base target.toAdr).accessedStorageKeys
          target.toAdr sevm.currentTarget.toB256) = _
    rw [temporalAccountAccessBase_accessedStorageKeys]
  obtain ⟨post2, hrun2, hstk2, hmem2, hgas2, herr2, hout2, hret2, hlogs2,
    hrefund2, hatd2, htrans2, hask2, haa2, heffect2, st₂, hsub2,
    hstate2⟩ :=
    gatewayQuery_statcall_crossing (sevm := sevm)
      (devm := post1.setMach
        ⟨[Nat.toB256 (Gb + 382), target, 284, 4, 0, 32],
          ((M.write 256 pauseForSelector.toBytes).write 288
            duration.toBytes).write 256 isPausedSelector.toBytes,
          Gb + 382⟩)
      (target := target) (iiw := 284) (isw := 4) (oiw := 0) (osw := 32)
      (storedUntil := pauseForProjection sevm.benvStat.time duration)
      (s := []) (G := Gb + 382)
      rfl rfl
      (by
        show (post1.setMach
          ⟨[Nat.toB256 (Gb + 382), target, 284, 4, 0, 32],
            ((M.write 256 pauseForSelector.toBytes).write 288
              duration.toBytes).write 256 isPausedSelector.toBytes,
            Gb + 382⟩).extCost _ = 0
        exact Devm.extCost_covered (by rw [hsize3]; decide))
      (by
        show post1.state.getCode target.toAdr = gatewayCode controlDeployParams
        exact hcode1)
      ((haa1 target.toAdr).mpr
        (temporalAccountAccessBase_warm base target.toAdr))
      (by
        simp only [Devm.memory_setMach]
        rw [Mem.extends_covered (by rw [hsize3]; decide)]
        exact hqueryWindow)
      (by simpa only [Devm.getStorVal_setMach] using heffect1)
      (by
        change (target.toAdr, resumeSinceSlot) ∈ post1.accessedStorageKeys
        rw [hask1']
        exact gatewayPauseKeys_union_resume_mem base.accessedStorageKeys
          target.toAdr sevm.currentTarget.toB256)
      hpaused hdepth hnp (by omega) (by omega) (by simp)
  have hgas2' : post2.gasLeft = Gb + 62 := by
    rw [hgas2]
    omega
  have hmem2' : post2.memory = pauseDecodedMemory M duration := by
    simp only [Devm.memory_setMach] at hmem2
    rw [hmem2,
      show (1 : B256).toBytes.take ((32 : B256)).toNat =
        (1 : B256).toBytes by decide,
      show ((0 : B256)).toNat = 0 by decide,
      Mem.extends_covered (by rw [hsize3]; decide)]
    rfl
  have heta2 : post2 = post2.setMach ⟨[1], pauseDecodedMemory M duration,
      Gb + 62⟩ := by
    rw [← hstk2, ← hmem2', ← hgas2']
    rfl
  have hltFlag : (Nat.toB256 post2.returnData.length <? (32 : B256)) =
      0 := by
    rw [hret2, B256.length_toBytes]
    decide
  have herrB : post2.error = base.error := by
    rw [herr2]
    show post1.error = base.error
    rw [herr1]
    exact temporalAccountAccessBase_error base target.toAdr
  have houtB : post2.output = base.output := by
    rw [hout2]
    show post1.output = base.output
    rw [hout1]
    exact temporalAccountAccessBase_output base target.toAdr
  have hlogsB : post2.logs =
      base.logs ++ [gatewayPauseEvent target.toAdr duration] := by
    rw [hlogs2]
    show post1.logs = base.logs ++ [gatewayPauseEvent target.toAdr duration]
    rw [hlogs1]
    change (temporalAccountAccessBase base target.toAdr).logs ++
      [gatewayPauseEvent target.toAdr duration] = _
    rw [temporalAccountAccessBase_logs]
  have hrefundB : post2.refundCounter = base.refundCounter := by
    rw [hrefund2]
    show post1.refundCounter = base.refundCounter
    rw [hrefund1]
    exact temporalAccountAccessBase_refundCounter base target.toAdr
  have hatdB : post2.accountsToDelete.isEmpty =
      base.accountsToDelete.isEmpty := by
    rw [hatd2]
    show post1.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty
    rw [hatd1]
    exact congrArg Std.HashSet.isEmpty
      (temporalAccountAccessBase_accountsToDelete base target.toAdr)
  have htransB : post2.transientStorage = base.transientStorage := by
    rw [htrans2]
    show post1.transientStorage = base.transientStorage
    rw [htrans1]
    exact temporalAccountAccessBase_transientStorage base target.toAdr
  have haskB : ∀ k, k ∈ post2.accessedStorageKeys ↔
      k ∈ base.accessedStorageKeys.union
        (gatewayPauseKeys base.accessedStorageKeys target.toAdr
          sevm.currentTarget.toB256) := by
    intro k
    rw [hask2 k]
    change k ∈ post1.accessedStorageKeys ↔ _
    rw [hask1']
  have haaB : ∀ a, a ∈ post2.accessedAddresses ↔
      (a = target.toAdr ∨ a ∈ base.accessedAddresses) := by
    intro a
    refine (haa2 a).trans ((haa1 a).trans ?_)
    show a ∈ (temporalAccountAccessBase base target.toAdr
      ).accessedAddresses ↔ (a = target.toAdr ∨ a ∈ base.accessedAddresses)
    exact temporalAccountAccessBase_mem base target.toAdr a
  have hsub1' : base.state.subBal sevm.currentTarget 0 = some st₁ := by
    rw [← temporalAccountAccessBase_state base target.toAdr]
    exact hsub1
  have hsub2' :
      ((st₁.addBal target.toAdr 0).setStorVal target.toAdr resumeSinceSlot
        (pauseForProjection sevm.benvStat.time duration)).subBal
          sevm.currentTarget 0 =
          some st₂ := by
    rw [← hstate1]
    exact hsub2
  refine ⟨post2.setMach ⟨[], pauseDecodedMemory M duration, Gb - 19⟩,
    rfl, rfl, rfl, herrB, houtB, hret2, hlogsB, hrefundB, hatdB, htransB,
    haskB, haaB, ?_, ⟨st₁, st₂, hsub1', hsub2', hstate2⟩, ?_⟩
  · simpa only [Devm.getStorVal_setMach] using heffect2
  intro post hwalk
  have hC : Func.RunCompiled fs sevm
      (post2.setMach ⟨[1], pauseDecodedMemory M duration, Gb + 62⟩)
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult)) post := by
    have hisz : ((pauseDecodedMemory M duration).read 0 32).1.toB256 =? 0 =
        (0 : B256) := by
      rw [hdecodedValue]
      decide
    have heq : (1 : B256) =?
        ((pauseDecodedMemory M duration).read 0 32).1.toB256 = 1 := by
      rw [hdecodedValue]
      decide
    have hG61 : 61 ≤ Gb + 62 := by omega
    have hG64 : 64 ≤ Gb + 62 := by omega
    have hG67 : 67 ≤ Gb + 62 := by omega
    func_run (14) [0, 0, 3, 0, 1]
    case h_cost =>
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_zero_of_le (by omega) (by omega)]
      norm_num [gVerylow]
    case h_arm =>
      have hg : Gb + 62 - 81 = Gb - 19 := by omega
      rw [hg, show ((0 : B256) * 32).toNat = 0 from by decide,
        hdecodedMemory]
      exact hwalk
  have hQueryPost : Func.RunCompiled fs sevm
      (post2.setMach ⟨[1], pauseDecodedMemory M duration, Gb + 62⟩)
      installedQueryPost post := by
    simpa only [installedQueryPost] using hC
  have hQueryCross : Func.RunCompiled fs sevm
      (post1.setMach
        ⟨[Nat.toB256 (Gb + 382), target, 284, 4, 0, 32],
          ((M.write 256 pauseForSelector.toBytes).write 288
            duration.toBytes).write 256 isPausedSelector.toBytes,
          Gb + 382⟩)
      (Ninst.staticcall ::: installedQueryPost) post := by
    refine Func.RunCompiled.next hrun2 ?_
    rw [heta2]
    exact hQueryPost
  have hQueryStage : Func.RunCompiled fs sevm
      (post1.setMach
        ⟨[], ((M.write 256 pauseForSelector.toBytes).write 288
          duration.toBytes).write 256 isPausedSelector.toBytes, Gb + 401⟩)
      installedQueryStage post := by
    unfold installedQueryStage
    func_run (7) [3]
    all_goals try simp_rw [htargetMemory3]
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign3 (by
        have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
        omega)]
      norm_num [gVerylow]
    case a =>
      rw [htargetValue3]
      have hg : Gb + 401 - 19 = Gb + 382 := by omega
      rw [hg]
      exact hQueryCross
  have hQueryWrite : Func.RunCompiled fs sevm
      (post1.setMach ⟨[],
        (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
        Gb + 410⟩)
      installedQueryWrite post := by
    unfold installedQueryWrite
    have h := installedQueryWrite_runCompiled fs sevm post1
      isPausedSelector
      ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
      (Gb + 401) installedQueryStage post (by decide +kernel) halign2
      (by omega) hQueryStage
    simpa only [show Gb + 401 + 9 = Gb + 410 by omega] using h
  have hB : Func.RunCompiled fs sevm
      (post1.setMach ⟨[1],
        (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
        Gb + 426⟩)
      installedQueryPrelude post := by
    unfold installedQueryPrelude
    have h := installedQueryGuard_runCompiled fs sevm post1
      ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
      (Gb + 410) installedQueryWrite post hQueryWrite
    simpa only [show Gb + 410 + 16 = Gb + 426 by omega] using h
  have hA2 : Func.RunCompiled fs sevm
      ((temporalAccountAccessBase base target.toAdr).setMach
        ⟨[(gatewayCode controlDeployParams).size.toB256, target], M,
          Gb + gatewayPauseChildCost duration + 585⟩)
      installedGuardPrelude post := by
    have hCallCross : Func.RunCompiled fs sevm
        ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[Nat.toB256 (Gb + gatewayPauseChildCost duration + 526),
              target, 0, 284, 36, 0, 0],
            (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
            Gb + gatewayPauseChildCost duration + 526⟩)
        (Ninst.call ::: installedQueryPrelude) post := by
      refine Func.RunCompiled.next hrun1 ?_
      rw [heta1]
      exact hB
    have hCallStage : Func.RunCompiled fs sevm
        ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[], (M.write 256 pauseForSelector.toBytes).write 288
            duration.toBytes,
            Gb + gatewayPauseChildCost duration + 546⟩)
        installedCallStage post := by
      unfold installedCallStage
      have h := installedCallArgs_runCompiled fs sevm
        (temporalAccountAccessBase base target.toAdr) target
        ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
        (Gb + gatewayPauseChildCost duration + 526)
        (Ninst.call ::: installedQueryPrelude) post halign2
        (by rw [hsize2]; decide) htargetMemory2 htargetValue2 hCallCross
      simpa only [show Gb + gatewayPauseChildCost duration + 526 + 20 =
        Gb + gatewayPauseChildCost duration + 546 by omega] using h
    have hDurationWrite : Func.RunCompiled fs sevm
        ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[], M.write 256 pauseForSelector.toBytes,
            Gb + gatewayPauseChildCost duration + 558⟩)
        (loadWord durationWord +++ mstoreAt 9 +++ installedCallStage) post := by
      have h := installedDurationWrite_runCompiled fs sevm
        (temporalAccountAccessBase base target.toAdr) duration
        (M.write 256 pauseForSelector.toBytes)
        (Gb + gatewayPauseChildCost duration + 546)
        installedCallStage post (by omega)
        (by rw [hsize1]; decide) (by rw [hsize1]; decide)
        hdurationMemory1 hdurationValue1 hCallStage
      simpa only [show Gb + gatewayPauseChildCost duration + 546 + 12 =
        Gb + gatewayPauseChildCost duration + 558 by omega] using h
    have hSelectorWrite : Func.RunCompiled fs sevm
        ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[], M, Gb + gatewayPauseChildCost duration + 567⟩)
        (pushB256 pauseForSelector ::: mstoreAt 8 +++
          loadWord durationWord +++ mstoreAt 9 +++ installedCallStage) post := by
      have h := installedQueryWrite_runCompiled fs sevm
        (temporalAccountAccessBase base target.toAdr) pauseForSelector M
        (Gb + gatewayPauseChildCost duration + 558)
        (loadWord durationWord +++ mstoreAt 9 +++ installedCallStage) post
        (by decide +kernel) halign (by rw [hsize]; decide) hDurationWrite
      simpa only [show Gb + gatewayPauseChildCost duration + 558 + 9 =
        Gb + gatewayPauseChildCost duration + 567 by omega] using h
    unfold installedGuardPrelude
    have h := installedCodeGuard_runCompiled fs sevm
      (temporalAccountAccessBase base target.toAdr)
      (gatewayCode controlDeployParams).size.toB256 target M
      (Gb + gatewayPauseChildCost duration + 567)
      (pushB256 pauseForSelector ::: mstoreAt 8 +++
        loadWord durationWord +++ mstoreAt 9 +++ installedCallStage)
      post (by rw [hgatewaySize]; decide) hSelectorWrite
    simpa only [hgatewaySize,
      show Gb + gatewayPauseChildCost duration + 567 + 18 =
        Gb + gatewayPauseChildCost duration + 585 by omega] using h
  have hextStep : Ninst.RunCompiled sevm
      (base.setMach ⟨[target, target], M,
        Gb + gatewayPauseChildCost duration + 585 + codeCost⟩)
      Ninst.extcodesize
      ((temporalAccountAccessBase base target.toAdr).setMach
        ⟨[(gatewayCode controlDeployParams).size.toB256, target], M,
          Gb + gatewayPauseChildCost duration + 585⟩) := by
    have h := temporal_extcodesize_runCompiled (sevm := sevm) (base := base)
      (x := target) (v := (gatewayCode controlDeployParams).size.toB256) (stack := [target])
      (M := M) (G := Gb + gatewayPauseChildCost duration + 585)
      (by rw [hgatewayCode]) (by simp)
    rw [hcodeCost] at h
    exact h
  func_run (3) [3]
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega)]
    norm_num [gVerylow]
  case a =>
    rw [htargetValue0, htargetMemory0]
    have hg : Gb + gatewayPauseChildCost duration + 594 + codeCost - 9 =
        Gb + gatewayPauseChildCost duration + 585 + codeCost := by omega
    rw [hg]
    exact Func.RunCompiled.next hextStep hA2

end Blanc.Composition.LidoCircuitBreakerTwg
