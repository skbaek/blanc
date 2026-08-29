import Blanc.LidoCircuitBreakerPinnedTargetStubWalk

/-!
# Parent crossings for the pinned-target control stub

This module lifts the source-compiled child walks through the parent contract's
`CALL` and `STATICCALL` boundaries and supplies the installed-stub success seam.
-/

namespace Blanc.LidoCircuitBreaker.PinnedTargetStubWalk

open Jaune
open Jaune.Ninst Blanc.Ninst
open PinnedTargetControl

/-! ## Parent/child boundary helpers -/

/-- The delegation resolution returns the caller's world either unchanged or
with exactly the delegated address recorded as accessed; the world-meta
projection below reads off this one characterization. -/
private lemma accessDelegation_devm {devm d1 : Devm} {a dadr : Adr}
    {dp : Bool} {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1 = devm ∨ d1 = addAccessedAddress devm dadr := by
  unfold accessDelegation at h
  rcases hd : getDelegatedCodeAddress (devm.state.getCode a) with _ | adr <;>
    simp only [hd] at h
  · cases h
    exact .inl rfl
  · cases h
    exact .inr rfl

private lemma accessDelegation_worldMeta {devm d1 : Devm} {a dadr : Adr}
    {dp : Bool} {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1.transientStorage = devm.transientStorage ∧
      d1.accessedStorageKeys = devm.accessedStorageKeys := by
  rcases accessDelegation_devm h with hd | hd <;> subst hd <;>
    exact ⟨rfl, rfl⟩

private lemma state_subBal_stor {st stmid : State} {sender a : Adr}
    {value : B256} (h : st.subBal sender value = some stmid) :
    (stmid.get a).stor = (st.get a).stor := by
  unfold State.subBal at h
  split at h
  · contradiction
  · cases h
    exact State.setBal_get_stor

/-- The value-zero `CALL` crossing whose child is the source-compiled pinned
target stub on its cold `pauseFor(uint256)` route. -/
private lemma runCompiled_call_zero_value_stubPause
    {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw duration : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc =
      ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_code : code = stubCode)
    (h_mcs : 22166 ≤ mcs)
    (h_data : ((d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).read
        iiw.toNat isw.toNat).1 = pauseForCalldata duration)
    (h_current : d1.getStorVal cw.toAdr pausedUntilSlot = 0)
    (h_original : getOrigStorVal sevm cw.toAdr pausedUntilSlot = 0)
    (h_cold : (cw.toAdr, pausedUntilSlot) ∉ d1.accessedStorageKeys)
    (h_dynamic : sevm.isStatic = false)
    (h_new : sevm.benvStat.time + duration ≠ 0)
    (h_room : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat [] ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) + (mcs - 22166) ∧
      post.error = devm.error ∧
      post.output = devm.output ∧
      post.returnData = [] ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔
        k = (cw.toAdr, pausedUntilSlot) ∨
          k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ d1.accessedAddresses) ∧
      post.getStorVal cw.toAdr pausedUntilSlot =
        sevm.benvStat.time + duration ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = (stmid.addBal cw.toAdr 0).setStorVal cw.toAdr
          pausedUntilSlot (sevm.benvStat.time + duration) := by
  let p := callSpawnParent d1 (mcc + ext)
    iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := callSpawnMsg sevm p mcs cw.toAdr dadr
    iiw.toNat isw.toNat code dp
  have h_afford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    change ¬ (d1.getAcct sevm.currentTarget).bal < 0
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable msg rfl h_afford
  let benv' := (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  let child := initEvm (msg.withBenv benv')
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have hchildData : (msg.withBenv benv').data =
      pauseForCalldata duration := by
    change (p.memory.read iiw.toNat isw.toNat).1 = _
    rw [show p.memory = d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] from
        callSpawnParent_memory]
    exact h_data
  have hchildCurrent :
      (initDevm (msg.withBenv benv')).getStorVal cw.toAdr pausedUntilSlot =
        0 := by
    change ((stmid.addBal cw.toAdr 0).get cw.toAdr).stor.get
      pausedUntilSlot = 0
    unfold State.addBal
    rw [State.setBal_get_stor, state_subBal_stor hsub]
    exact h_current
  have hchildOriginal :
      getOrigStorVal (initSevm (msg.withBenv benv')) cw.toAdr
        pausedUntilSlot = 0 := by
    change getOrigStorVal sevm cw.toAdr pausedUntilSlot = 0
    exact h_original
  have hchildCold :
      (cw.toAdr, pausedUntilSlot) ∉
        (initDevm (msg.withBenv benv')).accessedStorageKeys := by
    change (cw.toAdr, pausedUntilSlot) ∉ p.accessedStorageKeys
    change (cw.toAdr, pausedUntilSlot) ∉ d1.accessedStorageKeys
    exact h_cold
  have hchildCost : gasColdSload + sstoreValueCost
      (getOrigStorVal (initSevm (msg.withBenv benv')) cw.toAdr
        pausedUntilSlot)
      ((initDevm (msg.withBenv benv')).getStorVal cw.toAdr pausedUntilSlot)
      ((initSevm (msg.withBenv benv')).benvStat.time + duration) =
        22100 := by
    rw [hchildOriginal, hchildCurrent]
    change gasColdSload + sstoreValueCost 0 0
      (sevm.benvStat.time + duration) = 22100
    rw [sstoreValueCost,
      if_pos ⟨rfl, fun h => h_new h.symm⟩, if_pos rfl]
    norm_num [gasColdSload, gasStorageSet]
  obtain ⟨out, hexec, herr, hout, hgasOut, hmetaOut, hworldOut,
    heffectOut⟩ :=
    stubPause_exec (msg.withBenv benv') duration (mcs - 22166)
      (by change code = stubCode; exact h_code) hchildData
      (by change mcs = mcs - 22166 + 22166; omega)
      hchildCold (by change sevm.isStatic = false; exact h_dynamic)
      hchildCost
  have hlogsOut : out.logs = [] := by
    rw [show out.logs =
      (stubPausePost (initSevm (msg.withBenv benv'))
        (initDevm (msg.withBenv benv')) duration).logs from
      congrArg (fun view => view.logs) hmetaOut]
    rw [stubPausePost_logs]
    rfl
  have hrefundOut : out.refundCounter = 0 := by
    rw [show out.refundCounter =
      (stubPausePost (initSevm (msg.withBenv benv'))
        (initDevm (msg.withBenv benv')) duration).refundCounter from
      congrArg (fun view => view.refundCounter) hmetaOut]
    rw [stubPausePost_refundCounter]
    change sstoreNewRefundCounter (sevm.benvStat.time + duration)
      (getOrigStorVal (initSevm (msg.withBenv benv')) cw.toAdr
        pausedUntilSlot)
      ((initDevm (msg.withBenv benv')).getStorVal cw.toAdr pausedUntilSlot)
      0 = 0
    rw [hchildOriginal, hchildCurrent]
    unfold sstoreNewRefundCounter
    rw [if_pos (fun h => h_new h.symm)]
    simp
    intro hz
    exact False.elim (h_new hz.symm)
  have hatdOut : out.accountsToDelete = Std.HashSet.emptyWithCapacity := by
    rw [show out.accountsToDelete =
      (stubPausePost (initSevm (msg.withBenv benv'))
        (initDevm (msg.withBenv benv')) duration).accountsToDelete from
      congrArg (fun view => view.accountsToDelete) hmetaOut]
    rw [stubPausePost_accountsToDelete]
    rfl
  have haaOut : out.accessedAddresses = p.accessedAddresses := by
    rw [show out.accessedAddresses =
      (stubPausePost (initSevm (msg.withBenv benv'))
        (initDevm (msg.withBenv benv')) duration).accessedAddresses from
      congrArg (fun view => view.accessedAddresses) hmetaOut]
    rw [stubPausePost_accessedAddresses]
    rfl
  have haskOut : out.accessedStorageKeys =
      p.accessedStorageKeys.insert (cw.toAdr, pausedUntilSlot) := by
    rw [show out.accessedStorageKeys =
      (stubPausePost (initSevm (msg.withBenv benv'))
        (initDevm (msg.withBenv benv')) duration).accessedStorageKeys from
      congrArg (fun view => view.accessedStorageKeys) hmetaOut]
    rw [stubPausePost_accessedStorageKeys]
    rfl
  have htransOut : out.transientStorage = p.transientStorage := by
    rw [show out.transientStorage =
      (stubPausePost (initSevm (msg.withBenv benv'))
        (initDevm (msg.withBenv benv')) duration).transientStorage from
      congrArg (fun world => world.transientStorage) hworldOut]
    rw [stubPausePost_transientStorage]
    rfl
  have hstateOut : out.state =
      (stmid.addBal cw.toAdr 0).setStorVal cw.toAdr pausedUntilSlot
        (sevm.benvStat.time + duration) := by
    rw [show out.state =
      (stubPausePost (initSevm (msg.withBenv benv'))
        (initDevm (msg.withBenv benv')) duration).state from
      congrArg (fun world => world.state) hworldOut]
    rw [stubPausePost_state]
    rfl
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok out := by
    rw [show exec child = .ok out from hexec]
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
      h_depth (by simpa [p, msg]) (by simpa [p, msg] using hres)
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
      k = (cw.toAdr, pausedUntilSlot) ∨ k ∈ devm.accessedStorageKeys
    rw [haskOut, show p.accessedStorageKeys = devm.accessedStorageKeys from
      hd1wm.2]
    constructor
    · intro hk
      rcases Std.HashSet.mem_union_iff.mp hk with hk | hk
      · exact Or.inr hk
      · rcases Std.HashSet.mem_insert.mp hk with he | hk
        · exact Or.inl (eq_of_beq he).symm
        · exact Or.inr hk
    · intro hk
      rcases hk with rfl | hk
      · exact Std.HashSet.mem_union_iff.mpr
          (Or.inr Std.HashSet.mem_insert_self)
      · exact Std.HashSet.mem_union_iff.mpr (Or.inl hk)
  · intro a
    change a ∈ p.accessedAddresses.union out.accessedAddresses ↔
      a ∈ d1.accessedAddresses
    rw [haaOut]
    exact ⟨fun h => (Std.HashSet.mem_union_iff.mp h).elim id id,
      fun h => Std.HashSet.mem_union_iff.mpr (Or.inl h)⟩
  · change out.getStorVal cw.toAdr pausedUntilSlot = _
    exact heffectOut
  · rw [← hd1state]
    have hsub' : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, callSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsub'
    exact hsub'
  · change out.state = _
    exact hstateOut

/-- Resolve the warm, non-delegated parent `CALL` completely.  The parent
charge is the warm access `100` plus the compiled stub's `22166`. -/
private lemma stubPause_call_crossing
    {sevm : Sevm} {devm : Devm} {target iiw isw oiw osw duration : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: target :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (hgas : devm.gasLeft = G)
    (hext : devm.extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0)
    (hcode : devm.getCode target.toAdr = stubCode)
    (hwarm : target.toAdr ∈ devm.accessedAddresses)
    (hdata : ((devm.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).read
        iiw.toNat isw.toNat).1 = pauseForCalldata duration)
    (hcurrent : devm.getStorVal target.toAdr pausedUntilSlot = 0)
    (horiginal : getOrigStorVal sevm target.toAdr pausedUntilSlot = 0)
    (hcold : (target.toAdr, pausedUntilSlot) ∉ devm.accessedStorageKeys)
    (hdynamic : sevm.isStatic = false)
    (hnew : sevm.benvStat.time + duration ≠ 0)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hfloor : 22617 ≤ G) (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat [] ∧
      post.gasLeft = G - 22266 ∧
      post.error = devm.error ∧
      post.output = devm.output ∧
      post.returnData = [] ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔
        k = (target.toAdr, pausedUntilSlot) ∨
          k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔
        a ∈ devm.accessedAddresses) ∧
      post.getStorVal target.toAdr pausedUntilSlot =
        sevm.benvStat.time + duration ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = (stmid.addBal target.toAdr 0).setStorVal target.toAdr
          pausedUntilSlot (sevm.benvStat.time + duration) := by
  have hnodel : getDelegatedCodeAddress
      ((devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr) = none := by
    rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = devm.getCode target.toAdr from rfl, hcode]
    have hsize : stubCode.size = 47 := by
      decide +kernel
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
      22166 ≤ mcs ∧ mcc + 0 ≤ G ∧
        G - (mcc + 0) + (mcs - 22166) = G - 22266 := by
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
  have hd0current : d0.getStorVal target.toAdr pausedUntilSlot = 0 := by
    exact hcurrent
  have hd0cold : (target.toAdr, pausedUntilSlot) ∉
      d0.accessedStorageKeys := by
    exact hcold
  obtain ⟨post, hrun, hstack, hmem, hgasl, herr, hout, hret, hlogs,
    hrefund, hatd, htrans, hask, haa, heffect, stmid, hsub, hstate⟩ :=
    runCompiled_call_zero_value_stubPause
      (gw := Nat.toB256 G) (cw := target) (duration := duration)
      hstk
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0 from hext)
      hdel hacc hsplit (by rw [hd0gas]; exact hcross) hdepth hnp
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = stubCode from hcode)
      hmcs (by simpa only [hd0mem] using hdata) hd0current horiginal hd0cold
      hdynamic hnew hroom
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

/-- The `STATICCALL` crossing whose child is the source-compiled pinned target
stub on its warm canonical-true query route. -/
private lemma runCompiled_statcall_stubQuery
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
    (h_code : code = stubCode)
    (h_mcs : 172 ≤ mcs)
    (h_data : ((d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).read
        iiw.toNat isw.toNat).1 = isPausedCalldata)
    (h_stored : d1.getStorVal tw.toAdr pausedUntilSlot = storedUntil)
    (h_warm : (tw.toAdr, pausedUntilSlot) ∈ d1.accessedStorageKeys)
    (h_paused : sevm.benvStat.time < storedUntil)
    (h_room : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .statcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) + (mcs - 172) ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ d1.accessedAddresses) ∧
      post.getStorVal tw.toAdr pausedUntilSlot = storedUntil ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal tw.toAdr 0 := by
  let p := callSpawnParent d1 (mcc + ext)
    iiw.toNat isw.toNat oiw.toNat osw.toNat
  let msg := statcallSpawnMsg sevm p mcs tw.toAdr dadr
    iiw.toNat isw.toNat code dp
  have h_afford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    change ¬ (d1.getAcct sevm.currentTarget).bal < 0
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable msg rfl h_afford
  let benv' := (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  let child := initEvm (msg.withBenv benv')
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  have hchildData : (msg.withBenv benv').data = isPausedCalldata := by
    change (p.memory.read iiw.toNat isw.toNat).1 = _
    rw [show p.memory = d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] from
        callSpawnParent_memory]
    exact h_data
  have hchildStored :
      (initDevm (msg.withBenv benv')).getStorVal tw.toAdr pausedUntilSlot =
        storedUntil := by
    change ((stmid.addBal tw.toAdr 0).get tw.toAdr).stor.get
      pausedUntilSlot = storedUntil
    unfold State.addBal
    rw [State.setBal_get_stor, state_subBal_stor hsub]
    exact h_stored
  have hchildWarm :
      (tw.toAdr, pausedUntilSlot) ∈
        (initDevm (msg.withBenv benv')).accessedStorageKeys := by
    change (tw.toAdr, pausedUntilSlot) ∈ p.accessedStorageKeys
    change (tw.toAdr, pausedUntilSlot) ∈ d1.accessedStorageKeys
    exact h_warm
  obtain ⟨out, hexec, herr, hout, hgasOut, hmetaOut, hworldOut,
    heffectOut⟩ :=
    stubQuery_exec (msg.withBenv benv') storedUntil (mcs - 172)
      (by change code = stubCode; exact h_code) hchildData
      (by change mcs = mcs - 172 + 172; omega)
      hchildStored hchildWarm
      (by change sevm.benvStat.time < storedUntil; exact h_paused)
  have hlogsOut : out.logs = [] := by
    rw [show out.logs =
      ((initDevm (msg.withBenv benv')).withOutput
        (1 : B256).toBytes).logs from
      congrArg (fun view => view.logs) hmetaOut]
    rfl
  have hrefundOut : out.refundCounter = 0 := by
    rw [show out.refundCounter =
      ((initDevm (msg.withBenv benv')).withOutput
        (1 : B256).toBytes).refundCounter from
      congrArg (fun view => view.refundCounter) hmetaOut]
    rfl
  have hatdOut : out.accountsToDelete = Std.HashSet.emptyWithCapacity := by
    rw [show out.accountsToDelete =
      ((initDevm (msg.withBenv benv')).withOutput
        (1 : B256).toBytes).accountsToDelete from
      congrArg (fun view => view.accountsToDelete) hmetaOut]
    rfl
  have haaOut : out.accessedAddresses = p.accessedAddresses := by
    rw [show out.accessedAddresses =
      ((initDevm (msg.withBenv benv')).withOutput
        (1 : B256).toBytes).accessedAddresses from
      congrArg (fun view => view.accessedAddresses) hmetaOut]
    rfl
  have haskOut : out.accessedStorageKeys = p.accessedStorageKeys := by
    rw [show out.accessedStorageKeys =
      ((initDevm (msg.withBenv benv')).withOutput
        (1 : B256).toBytes).accessedStorageKeys from
      congrArg (fun view => view.accessedStorageKeys) hmetaOut]
    rfl
  have htransOut : out.transientStorage = p.transientStorage := by
    rw [show out.transientStorage =
      (initDevm (msg.withBenv benv')).transientStorage from
      congrArg (fun world => world.transientStorage) hworldOut]
    rfl
  have hstateOut : out.state = stmid.addBal tw.toAdr 0 := by
    rw [show out.state = (initDevm (msg.withBenv benv')).state from
      congrArg (fun world => world.state) hworldOut]
    rfl
  have hsettle : (Frame.ofCall msg).settle (exec child) = .ok out := by
    rw [show exec child = .ok out from hexec]
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
  have hrun : Ninst.RunCompiled sevm devm (.exec .statcall) post :=
    Ninst.runCompiled_exec_run
      (Xinst.step_statcall_spawn h_stk h_ext h_del h_acc h_split h_gas
        h_depth)
      (by simpa [p, msg] using henter) (by simpa [p, msg] using hres)
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
  · change out.getStorVal tw.toAdr pausedUntilSlot = storedUntil
    exact heffectOut
  · rw [← hd1state]
    have hsub' : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, statcallSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsub'
    exact hsub'
  · change out.state = stmid.addBal tw.toAdr 0
    exact hstateOut

/-- Resolve the warm, non-delegated parent `STATICCALL` completely.  The
parent charge is the warm access `100` plus the compiled stub's `172`. -/
private lemma stubQuery_statcall_crossing
    {sevm : Sevm} {devm : Devm} {target iiw isw oiw osw storedUntil : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: target :: iiw :: isw :: oiw :: osw :: s)
    (hgas : devm.gasLeft = G)
    (hext : devm.extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0)
    (hcode : devm.getCode target.toAdr = stubCode)
    (hwarm : target.toAdr ∈ devm.accessedAddresses)
    (hdata : ((devm.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).read
        iiw.toNat isw.toNat).1 = isPausedCalldata)
    (hstored : devm.getStorVal target.toAdr pausedUntilSlot = storedUntil)
    (hwarmSlot : (target.toAdr, pausedUntilSlot) ∈
      devm.accessedStorageKeys)
    (hpaused : sevm.benvStat.time < storedUntil)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hfloor : 274 ≤ G) (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .statcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = G - 272 ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ devm.accessedAddresses) ∧
      post.getStorVal target.toAdr pausedUntilSlot = storedUntil ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal target.toAdr 0 := by
  have hnodel : getDelegatedCodeAddress
      ((devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr) = none := by
    rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = devm.getCode target.toAdr from rfl, hcode]
    have hsize : stubCode.size = 47 := by
      decide +kernel
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
      172 ≤ mcs ∧ mcc + 0 ≤ G ∧
        G - (mcc + 0) + (mcs - 172) = G - 272 := by
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
  have hd0stored : d0.getStorVal target.toAdr pausedUntilSlot =
      storedUntil := by exact hstored
  have hd0warmSlot : (target.toAdr, pausedUntilSlot) ∈
      d0.accessedStorageKeys := by exact hwarmSlot
  obtain ⟨post, hrun, hstack, hmem, hgasl, herr, hout, hret, hlogs,
    hrefund, hatd, htrans, hask, haa, heffect, stmid, hsub, hstate⟩ :=
    runCompiled_statcall_stubQuery
      (gw := Nat.toB256 G) (tw := target) (storedUntil := storedUntil)
      hstk
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0 from hext)
      hdel hacc hsplit (by rw [hd0gas]; exact hcross) hdepth hnp
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = stubCode from hcode)
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

private lemma state_setStorVal_getCode (st : State) (owner a : Adr)
    (key value : B256) :
    (st.setStorVal owner key value).getCode a = st.getCode a := by
  unfold State.getCode
  have h := congrFun
    (State.setStorVal_balCodeEq st owner key value) a
  exact (congrArg Prod.snd h).symm

/-! ## The installed-stub pause suffix -/

private def installedQueryPost : Func :=
  Ninst.iszero :::
    ((Func.call bubbleRevertSlot) <?> decodePausedResult)

private def installedQueryStage : Func :=
  pushList [32, 0, 4, 0x11c] +++ loadWord targetWord +++
    Ninst.gas ::: Ninst.statcall ::: installedQueryPost

private def installedQueryWrite : Func :=
  pushB256 isPausedSelector ::: mstoreAt 8 +++ installedQueryStage

private def installedQueryPrelude : Func :=
  Ninst.iszero :::
    ((Func.call bubbleRevertSlot) <?> installedQueryWrite)

private def installedCallStage : Func :=
  pushList [0, 0, 36, 0x11c, 0] +++ loadWord targetWord +++
    Ninst.gas ::: Ninst.call ::: installedQueryPrelude

private def installedGuardPrelude : Func :=
  Ninst.iszero :::
    ((Func.call emptyRevertSlot) <?>
      (Ninst.pop :::
        pushB256 pauseForSelector ::: mstoreAt 8 +++
        loadWord durationWord +++ mstoreAt 9 +++ installedCallStage))

private theorem installedQueryGuard_runCompiled
    (fs : List Func) (sevm : Sevm) (devm : Devm) (M : Mem)
    (G : Nat) (tail : Func) (post : Devm)
    (htail : Func.RunCompiled fs sevm
      (devm.setMach ⟨[], M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (devm.setMach ⟨[1], M, G + 16⟩)
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> tail)) post := by
  func_run (2) [0]
  case h_arm =>
    have hg : G + 16 - 16 = G := by omega
    rw [hg]
    exact htail

private theorem installedQueryWrite_runCompiled
    (fs : List Func) (sevm : Sevm) (devm : Devm) (value : B256) (M : Mem)
    (G : Nat) (tail : Func) (post : Devm)
    (hvalue : value ≠ 0)
    (halign : M.size % 32 = 0)
    (hcover : 256 + 32 ≤ M.size)
    (htail : Func.RunCompiled fs sevm
      (devm.setMach ⟨[], M.write 256 value.toBytes, G⟩)
      tail post) :
    Func.RunCompiled fs sevm
      (devm.setMach ⟨[], M, G + 9⟩)
      (pushB256 value ::: mstoreAt 8 +++ tail) post := by
  have hpush : Ninst.RunCompiled sevm
      (devm.setMach ⟨[], M, G + 9⟩) (pushB256 value)
      (devm.setMach ⟨[value], M, G + 6⟩) :=
    Ninst.runCompiled_pushB256 (w := value) (c := 3) (G := G + 6)
      (by simpa only [gVerylow] using pushCost_of_ne_zero hvalue)
      (by show G + 9 = G + 6 + 3; omega)
      (by show ([] : List B256).length < 1024; decide)
  refine Func.RunCompiled.next hpush ?_
  func_run (2) [0]
  all_goals try simp_rw [show ((8 : B256) * 32).toNat = 256 by decide]
  case h_ext =>
    exact Devm.extCost_zero_of_le halign hcover
  case a =>
    have hg : G + 6 - 6 = G := by omega
    rw [hg]
    exact htail

private theorem installedCallArgs_runCompiled
    (fs : List Func) (sevm : Sevm) (devm : Devm)
    (target : B256) (M : Mem) (G : Nat) (tail : Func) (post : Devm)
    (halign : M.size % 32 = 0)
    (hcover : (targetWord * 32).toNat + 32 ≤ M.size)
    (hreadMemory : (M.read (targetWord * 32).toNat 32).2 = M)
    (hreadValue : (M.read (targetWord * 32).toNat 32).1.toB256 = target)
    (htail : Func.RunCompiled fs sevm
      (devm.setMach
        ⟨[Nat.toB256 G, target, 0, 284, 36, 0, 0], M, G⟩)
      tail post) :
    Func.RunCompiled fs sevm (devm.setMach ⟨[], M, G + 20⟩)
      (pushList [0, 0, 36, 0x11c, 0] +++ loadWord targetWord +++
        Ninst.gas ::: tail) post := by
  func_run (8) [3]
  all_goals try simp_rw [hreadMemory]
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hcover]
    norm_num [gVerylow]
  case a =>
    rw [hreadValue]
    have hg : G + 20 - 20 = G := by omega
    rw [hg]
    exact htail

private theorem installedDurationWrite_runCompiled
    (fs : List Func) (sevm : Sevm) (devm : Devm)
    (duration : B256) (M : Mem) (G : Nat) (tail : Func) (post : Devm)
    (halign : M.size % 32 = 0)
    (hreadCover : (durationWord * 32).toNat + 32 ≤ M.size)
    (hwriteCover : 288 + 32 ≤ M.size)
    (hreadMemory : (M.read (durationWord * 32).toNat 32).2 = M)
    (hreadValue : (M.read (durationWord * 32).toNat 32).1.toB256 = duration)
    (htail : Func.RunCompiled fs sevm
      (devm.setMach ⟨[], M.write 288 duration.toBytes, G⟩) tail post) :
    Func.RunCompiled fs sevm (devm.setMach ⟨[], M, G + 12⟩)
      (loadWord durationWord +++ mstoreAt 9 +++ tail) post := by
  func_run (4) [3, 0]
  all_goals try simp_rw [show ((9 : B256) * 32).toNat = 288 by decide]
  all_goals try simp_rw [hreadMemory]
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hreadCover]
    norm_num [gVerylow]
  case h_ext =>
    exact Devm.extCost_zero_of_le halign hwriteCover
  case a =>
    rw [hreadValue]
    have hg : G + 12 - 12 = G := by omega
    rw [hg]
    exact htail

private theorem installedCodeGuard_runCompiled
    (fs : List Func) (sevm : Sevm) (devm : Devm)
    (target : B256) (M : Mem) (G : Nat) (tail : Func) (post : Devm)
    (htail : Func.RunCompiled fs sevm
      (devm.setMach ⟨[], M, G⟩) tail post) :
    Func.RunCompiled fs sevm
      (devm.setMach ⟨[(47 : B256), target], M, G + 18⟩)
      (Ninst.iszero :::
        ((Func.call emptyRevertSlot) <?> (Ninst.pop ::: tail))) post := by
  func_run (3) [0]
  case a =>
    have hg : G + 18 - 18 = G := by omega
    rw [hg]
    exact htail

/-- The complete `pauseAfterSet` suffix when both external boundaries execute
the installed source-compiled pinned-target stub. -/
theorem pauseAfterSet_stub_toSuccess_runCompiled
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
    (hstubCode : base.getCode target.toAdr = stubCode)
    (hcurrent : base.getStorVal target.toAdr pausedUntilSlot = 0)
    (horiginal : getOrigStorVal sevm target.toAdr pausedUntilSlot = 0)
    (hcold : (target.toAdr, pausedUntilSlot) ∉ base.accessedStorageKeys)
    (hdynamic : sevm.isStatic = false)
    (hnew : sevm.benvStat.time + duration ≠ 0)
    (hpaused : sevm.benvStat.time < sevm.benvStat.time + duration)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hbound : Gb + 22663 < 2 ^ 256) :
    ∃ mid : Devm,
      mid.stack = [] ∧
      mid.memory = pauseDecodedMemory M duration ∧
      mid.gasLeft = Gb ∧
      mid.error = base.error ∧
      mid.output = base.output ∧
      mid.returnData = (1 : B256).toBytes ∧
      mid.logs = base.logs ∧
      mid.refundCounter = base.refundCounter ∧
      mid.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty ∧
      mid.transientStorage = base.transientStorage ∧
      (∀ k, k ∈ mid.accessedStorageKeys ↔
        k = (target.toAdr, pausedUntilSlot) ∨
          k ∈ base.accessedStorageKeys) ∧
      (∀ a, a ∈ mid.accessedAddresses ↔
        (a = target.toAdr ∨ a ∈ base.accessedAddresses)) ∧
      mid.getStorVal target.toAdr pausedUntilSlot =
        sevm.benvStat.time + duration ∧
      (∃ st₁ st₂ : State,
        base.state.subBal sevm.currentTarget 0 = some st₁ ∧
        ((st₁.addBal target.toAdr 0).setStorVal target.toAdr
          pausedUntilSlot (sevm.benvStat.time + duration)).subBal
            sevm.currentTarget 0 = some st₂ ∧
        mid.state = st₂.addBal target.toAdr 0) ∧
      ∀ post : Devm,
        Func.RunCompiled fs sevm mid pauseSuccess post →
        Func.RunCompiled fs sevm
          (base.setMach ⟨[], M, Gb + 22731 + codeCost⟩)
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
        duration.toBytes).read 284 36).1 = pauseForCalldata duration := by
    rw [Mem.Reads.read hreads2]
    exact sliceD_stagedCalldata img pauseForSelector duration
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
          284 4).1 = isPausedCalldata := by
    rw [Mem.Reads.read hreads3]
    exact sliceD_stagedSelector
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
  have hstubSize : stubCode.size.toB256 = (47 : B256) := by
    have hs : stubCode.size = 47 := by decide +kernel
    rw [hs]
    decide +kernel
  obtain ⟨post1, hrun1, hstk1, hmem1, hgas1, herr1, hout1, hret1, hlogs1,
    hrefund1, hatd1, htrans1, hask1, haa1, heffect1, st₁, hsub1,
    hstate1⟩ :=
    stubPause_call_crossing (sevm := sevm)
      (devm := (temporalAccountAccessBase base target.toAdr).setMach
        ⟨[Nat.toB256 (Gb + 22663), target, 0, 284, 36, 0, 0],
          (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
          Gb + 22663⟩)
      (target := target) (iiw := 284) (isw := 36) (oiw := 0) (osw := 0)
      (duration := duration) (s := []) (G := Gb + 22663)
      rfl rfl
      (by
        show ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[Nat.toB256 (Gb + 22663), target, 0, 284, 36, 0, 0],
            (M.write 256 pauseForSelector.toBytes).write 288
              duration.toBytes, Gb + 22663⟩).extCost _ = 0
        exact Devm.extCost_covered (by rw [hsize2]; decide))
      (by
        show (temporalAccountAccessBase base target.toAdr).getCode
          target.toAdr = stubCode
        rw [temporalAccountAccessBase_getCode]
        exact hstubCode)
      (temporalAccountAccessBase_warm base target.toAdr)
      (by
        simp only [Devm.memory_setMach]
        rw [Mem.extends_covered (by rw [hsize2]; decide)]
        exact hpauseWindow)
      (by
        show (temporalAccountAccessBase base target.toAdr).getStorVal
          target.toAdr pausedUntilSlot = 0
        simpa only [Devm.getStorVal, Devm.getAcct,
          temporalAccountAccessBase_state] using hcurrent)
      horiginal
      (by
        change (target.toAdr, pausedUntilSlot) ∉
          (temporalAccountAccessBase base target.toAdr).accessedStorageKeys
        rw [temporalAccountAccessBase_accessedStorageKeys]
        exact hcold)
      hdynamic hnew hdepth hnp (by omega) hbound (by simp)
  have hgas1' : post1.gasLeft = Gb + 397 := by
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
      Gb + 397⟩ := by
    rw [← hstk1, ← hmem1', ← hgas1']
    rfl
  have hcode1 : post1.state.getCode target.toAdr = stubCode := by
    rw [hstate1, state_setStorVal_getCode, State.addBal_getCode,
      State.subBal_getCode hsub1]
    show (temporalAccountAccessBase base target.toAdr).state.getCode
      target.toAdr = stubCode
    rw [temporalAccountAccessBase_state]
    exact hstubCode
  obtain ⟨post2, hrun2, hstk2, hmem2, hgas2, herr2, hout2, hret2, hlogs2,
    hrefund2, hatd2, htrans2, hask2, haa2, heffect2, st₂, hsub2,
    hstate2⟩ :=
    stubQuery_statcall_crossing (sevm := sevm)
      (devm := post1.setMach
        ⟨[Nat.toB256 (Gb + 353), target, 284, 4, 0, 32],
          ((M.write 256 pauseForSelector.toBytes).write 288
            duration.toBytes).write 256 isPausedSelector.toBytes,
          Gb + 353⟩)
      (target := target) (iiw := 284) (isw := 4) (oiw := 0) (osw := 32)
      (storedUntil := sevm.benvStat.time + duration)
      (s := []) (G := Gb + 353)
      rfl rfl
      (by
        show (post1.setMach
          ⟨[Nat.toB256 (Gb + 353), target, 284, 4, 0, 32],
            ((M.write 256 pauseForSelector.toBytes).write 288
              duration.toBytes).write 256 isPausedSelector.toBytes,
            Gb + 353⟩).extCost _ = 0
        exact Devm.extCost_covered (by rw [hsize3]; decide))
      (by
        show post1.state.getCode target.toAdr = stubCode
        exact hcode1)
      ((haa1 target.toAdr).mpr
        (temporalAccountAccessBase_warm base target.toAdr))
      (by
        simp only [Devm.memory_setMach]
        rw [Mem.extends_covered (by rw [hsize3]; decide)]
        exact hqueryWindow)
      (by simpa only [Devm.getStorVal_setMach] using heffect1)
      (by
        apply (hask1 (target.toAdr, pausedUntilSlot)).mpr
        exact Or.inl rfl)
      hpaused hdepth hnp (by omega) (by omega) (by simp)
  have hgas2' : post2.gasLeft = Gb + 81 := by
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
      Gb + 81⟩ := by
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
  have hlogsB : post2.logs = base.logs := by
    rw [hlogs2]
    show post1.logs = base.logs
    rw [hlogs1]
    exact temporalAccountAccessBase_logs base target.toAdr
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
      k = (target.toAdr, pausedUntilSlot) ∨
        k ∈ base.accessedStorageKeys := by
    intro k
    rw [hask2 k]
    change k ∈ post1.accessedStorageKeys ↔ _
    rw [hask1 k]
    change (k = (target.toAdr, pausedUntilSlot) ∨
      k ∈ (temporalAccountAccessBase base target.toAdr).accessedStorageKeys) ↔ _
    rw [temporalAccountAccessBase_accessedStorageKeys]
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
      ((st₁.addBal target.toAdr 0).setStorVal target.toAdr pausedUntilSlot
        (sevm.benvStat.time + duration)).subBal sevm.currentTarget 0 =
          some st₂ := by
    rw [← hstate1]
    exact hsub2
  refine ⟨post2.setMach ⟨[], pauseDecodedMemory M duration, Gb⟩,
    rfl, rfl, rfl, herrB, houtB, hret2, hlogsB, hrefundB, hatdB, htransB,
    haskB, haaB, ?_, ⟨st₁, st₂, hsub1', hsub2', hstate2⟩, ?_⟩
  · simpa only [Devm.getStorVal_setMach] using heffect2
  intro post hwalk
  have hC : Func.RunCompiled fs sevm
      (post2.setMach ⟨[1], pauseDecodedMemory M duration, Gb + 81⟩)
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
    func_run (14) [0, 0, 3, 0, 1]
    case h_cost =>
      simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_zero_of_le (by omega) (by omega)]
      norm_num [gVerylow]
    case h_arm =>
      have hg : Gb + 81 - 81 = Gb := by omega
      rw [hg, show ((0 : B256) * 32).toNat = 0 from by decide,
        hdecodedMemory]
      exact hwalk
  have hQueryPost : Func.RunCompiled fs sevm
      (post2.setMach ⟨[1], pauseDecodedMemory M duration, Gb + 81⟩)
      installedQueryPost post := by
    simpa only [installedQueryPost] using hC
  have hQueryCross : Func.RunCompiled fs sevm
      (post1.setMach
        ⟨[Nat.toB256 (Gb + 353), target, 284, 4, 0, 32],
          ((M.write 256 pauseForSelector.toBytes).write 288
            duration.toBytes).write 256 isPausedSelector.toBytes,
          Gb + 353⟩)
      (Ninst.statcall ::: installedQueryPost) post := by
    refine Func.RunCompiled.next hrun2 ?_
    rw [heta2]
    exact hQueryPost
  have hQueryStage : Func.RunCompiled fs sevm
      (post1.setMach
        ⟨[], ((M.write 256 pauseForSelector.toBytes).write 288
          duration.toBytes).write 256 isPausedSelector.toBytes, Gb + 372⟩)
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
      have hg : Gb + 372 - 19 = Gb + 353 := by omega
      rw [hg]
      exact hQueryCross
  have hQueryWrite : Func.RunCompiled fs sevm
      (post1.setMach ⟨[],
        (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
        Gb + 381⟩)
      installedQueryWrite post := by
    unfold installedQueryWrite
    have h := installedQueryWrite_runCompiled fs sevm post1
      isPausedSelector
      ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
      (Gb + 372) installedQueryStage post (by decide +kernel) halign2
      (by omega) hQueryStage
    simpa only [show Gb + 372 + 9 = Gb + 381 by omega] using h
  have hB : Func.RunCompiled fs sevm
      (post1.setMach ⟨[1],
        (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
        Gb + 397⟩)
      installedQueryPrelude post := by
    unfold installedQueryPrelude
    have h := installedQueryGuard_runCompiled fs sevm post1
      ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
      (Gb + 381) installedQueryWrite post hQueryWrite
    simpa only [show Gb + 381 + 16 = Gb + 397 by omega] using h
  have hA2 : Func.RunCompiled fs sevm
      ((temporalAccountAccessBase base target.toAdr).setMach
        ⟨[stubCode.size.toB256, target], M, Gb + 22722⟩)
      installedGuardPrelude post := by
    have hCallCross : Func.RunCompiled fs sevm
        ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[Nat.toB256 (Gb + 22663), target, 0, 284, 36, 0, 0],
            (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
            Gb + 22663⟩)
        (Ninst.call ::: installedQueryPrelude) post := by
      refine Func.RunCompiled.next hrun1 ?_
      rw [heta1]
      exact hB
    have hCallStage : Func.RunCompiled fs sevm
        ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[], (M.write 256 pauseForSelector.toBytes).write 288
            duration.toBytes, Gb + 22683⟩)
        installedCallStage post := by
      unfold installedCallStage
      have h := installedCallArgs_runCompiled fs sevm
        (temporalAccountAccessBase base target.toAdr) target
        ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
        (Gb + 22663) (Ninst.call ::: installedQueryPrelude) post halign2
        (by rw [hsize2]; decide) htargetMemory2 htargetValue2 hCallCross
      simpa only [show Gb + 22663 + 20 = Gb + 22683 by omega] using h
    have hDurationWrite : Func.RunCompiled fs sevm
        ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[], M.write 256 pauseForSelector.toBytes, Gb + 22695⟩)
        (loadWord durationWord +++ mstoreAt 9 +++ installedCallStage) post := by
      have h := installedDurationWrite_runCompiled fs sevm
        (temporalAccountAccessBase base target.toAdr) duration
        (M.write 256 pauseForSelector.toBytes) (Gb + 22683)
        installedCallStage post (by omega)
        (by rw [hsize1]; decide) (by rw [hsize1]; decide)
        hdurationMemory1 hdurationValue1 hCallStage
      simpa only [show Gb + 22683 + 12 = Gb + 22695 by omega] using h
    have hSelectorWrite : Func.RunCompiled fs sevm
        ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[], M, Gb + 22704⟩)
        (pushB256 pauseForSelector ::: mstoreAt 8 +++
          loadWord durationWord +++ mstoreAt 9 +++ installedCallStage) post := by
      have h := installedQueryWrite_runCompiled fs sevm
        (temporalAccountAccessBase base target.toAdr) pauseForSelector M
        (Gb + 22695)
        (loadWord durationWord +++ mstoreAt 9 +++ installedCallStage) post
        (by decide +kernel) halign (by rw [hsize]; decide) hDurationWrite
      simpa only [show Gb + 22695 + 9 = Gb + 22704 by omega] using h
    unfold installedGuardPrelude
    have h := installedCodeGuard_runCompiled fs sevm
      (temporalAccountAccessBase base target.toAdr) target M (Gb + 22704)
      (pushB256 pauseForSelector ::: mstoreAt 8 +++
        loadWord durationWord +++ mstoreAt 9 +++ installedCallStage)
      post hSelectorWrite
    simpa only [hstubSize,
      show Gb + 22704 + 18 = Gb + 22722 by omega] using h
  have hextStep : Ninst.RunCompiled sevm
      (base.setMach ⟨[target, target], M, Gb + 22722 + codeCost⟩)
      Ninst.extcodesize
      ((temporalAccountAccessBase base target.toAdr).setMach
        ⟨[stubCode.size.toB256, target], M, Gb + 22722⟩) := by
    have h := temporal_extcodesize_runCompiled (sevm := sevm) (base := base)
      (x := target) (v := stubCode.size.toB256) (stack := [target])
      (M := M) (G := Gb + 22722)
      (by rw [hstubCode]) (by simp)
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
    have hg : Gb + 22731 + codeCost - 9 =
        Gb + 22722 + codeCost := by omega
    rw [hg]
    exact Func.RunCompiled.next hextStep hA2

end Blanc.LidoCircuitBreaker.PinnedTargetStubWalk
