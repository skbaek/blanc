import Blanc.ForwardCall

namespace Blanc

open Jaune

/-! ## Fixed-width SHA-256 precompile crossing -/

/-- SHA-256 charges exactly 84 gas on a 64-byte input and returns its digest. -/
theorem executeSha256_of_length_64 {evm : Evm}
    (hlen : evm.sta.data.length = 64)
    (hgas : 84 ≤ evm.dyna.gasLeft) :
    executeSha256 evm =
      .ok 84 (Bytes.sha256 evm.sta.data).toBytes := by
  simp only [executeSha256, hlen]
  norm_num [ceilDiv, PrecompResult.chargeGas, hgas]

/-- Address two selects the fixed-width SHA-256 result above. -/
theorem executePrecomp_two_of_length_64 {evm : Evm}
    (hlen : evm.sta.data.length = 64)
    (hgas : 84 ≤ evm.dyna.gasLeft) :
    executePrecomp evm 2 =
      applyPrecompResult evm
        (.ok 84 (Bytes.sha256 evm.sta.data).toBytes) := by
  unfold executePrecomp
  change applyPrecompResult evm (executeSha256 evm) = _
  rw [executeSha256_of_length_64 hlen hgas]

/-- A funded 64-byte SHA-256 message resolves synchronously at frame entry. -/
theorem Frame.enter_sha256_of_length_64 {f : Frame} {benv : Benv}
    (h_bt : f.inner.benvAfterTransfer = .ok benv)
    (h_ca : (f.inner.withBenv benv).codeAddress = some 2)
    (h_pre :
      (!((f.inner.withBenv benv).disablePrecompiles) &&
        decide ((f.inner.withBenv benv).benv.stat.rules.isPrecomp 2)) = true)
    (hlen : (initEvm (f.inner.withBenv benv)).sta.data.length = 64)
    (hgas : 84 ≤ (initEvm (f.inner.withBenv benv)).dyna.gasLeft) :
    f.enter = .done
      (f.settle
        (applyPrecompResult (initEvm (f.inner.withBenv benv))
          (.ok 84
            (Bytes.sha256 (initEvm (f.inner.withBenv benv)).sta.data).toBytes))) := by
  rw [Frame.enter_eq_done_executePrecomp h_bt h_ca h_pre,
    executePrecomp_two_of_length_64 hlen hgas]

/-- Assemble a successful 64-byte SHA-256 `STATICCALL` from the generic
call-frame pieces.  Arithmetic and delegation resolution remain explicit at
this layer; the warm covered-memory specialization below discharges them. -/
theorem Ninst.runCompiled_statcall_sha256_64
    {sevm : Sevm} {devm parent : Devm} {benv : Benv}
    {gw iiw oiw : B256} {s : List B256}
    {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack =
      gw :: (2 : B256) :: iiw :: (64 : B256) ::
        oiw :: (32 : B256) :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) 2) 2 =
        ⟨false, 2, code, dgc, d1⟩)
    (h_acc : accessCost 2
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses +
        dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc =
      ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_parent : parent = callSpawnParent d1 (mcc + ext)
      iiw.toNat 64 oiw.toNat 32)
    (h_bt : (statcallSpawnMsg sevm parent mcs 2 2
      iiw.toNat 64 code false).benvAfterTransfer = .ok benv)
    (h_pre :
      (!((statcallSpawnMsg sevm parent mcs 2 2
          iiw.toNat 64 code false).withBenv benv).disablePrecompiles &&
        decide (((statcallSpawnMsg sevm parent mcs 2 2
          iiw.toNat 64 code false).withBenv benv).benv.stat.rules.isPrecomp 2)) =
        true)
    (h_len : (initEvm ((statcallSpawnMsg sevm parent mcs 2 2
      iiw.toNat 64 code false).withBenv benv)).sta.data.length = 64)
    (h_shaGas : 84 ≤ mcs)
    (h_room : parent.stack.length < 1024) :
    let msg := statcallSpawnMsg sevm parent mcs 2 2
      iiw.toNat 64 code false
    let cev := initEvm (msg.withBenv benv)
    let child :=
      (cev.dyna.withGasLeft (cev.dyna.gasLeft - 84)).withOutput
        (Bytes.sha256 cev.sta.data).toBytes
    let post :=
      (((incorporateChildOnSuccess parent child child.output).setMach
        ⟨1 :: parent.stack, parent.memory,
          parent.gasLeft + child.gasLeft⟩).memWrite
            oiw.toNat (child.output.take 32))
    Ninst.RunCompiled sevm devm (.exec .statcall) post := by
  subst parent
  let p := callSpawnParent d1 (mcc + ext)
    iiw.toNat 64 oiw.toNat 32
  let msg := statcallSpawnMsg sevm p mcs 2 2
    iiw.toNat 64 code false
  let cev := initEvm (msg.withBenv benv)
  let child :=
    (cev.dyna.withGasLeft (cev.dyna.gasLeft - 84)).withOutput
      (Bytes.sha256 cev.sta.data).toBytes
  have hbt : msg.benvAfterTransfer = .ok benv := by
    simpa only [msg, p] using h_bt
  have hpre :
      (!((msg.withBenv benv).disablePrecompiles) &&
        decide ((msg.withBenv benv).benv.stat.rules.isPrecomp 2)) = true := by
    simpa only [msg, p] using h_pre
  have hlen : (initEvm (msg.withBenv benv)).sta.data.length = 64 := by
    simpa only [msg, p] using h_len
  have hfund : 84 ≤ (initEvm (msg.withBenv benv)).dyna.gasLeft := by
    change 84 ≤ mcs
    exact h_shaGas
  have henterRaw := Frame.enter_sha256_of_length_64
    (f := Frame.ofCall msg) (benv := benv)
    hbt (by rfl) hpre hlen hfund
  have henter :
      (Frame.ofCall msg).enter =
        .done ((Frame.ofCall msg).settle (.ok child)) := by
    simpa only [child, cev, applyPrecompResult, Frame.ofCall] using henterRaw
  have hsettle :
      (Frame.ofCall msg).settle (.ok child) = .ok child := by
    rfl
  have hroom : p.stack.length < 1024 := by
    simpa only [p] using h_room
  let post :=
    (((incorporateChildOnSuccess p child child.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft⟩).memWrite
        oiw.toNat (child.output.take 32))
  have hres : Resume.run (.call p oiw.toNat 32)
      ((Frame.ofCall msg).settle (.ok child)) = .ok post := by
    rw [hsettle, Resume.run_call_ok (by rfl) hroom]
  have h64 : (64 : B256).toNat = 64 := rfl
  have h32 : (32 : B256).toNat = 32 := rfl
  have h2adr : (2 : B256).toAdr = 2 := rfl
  have hrun : Ninst.RunCompiled sevm devm (.exec .statcall) post :=
    Ninst.runCompiled_statcall_doneFrame
      h_stk (by simpa only [h64, h32] using h_ext) h_del h_acc
      (by simpa using h_split) h_gas h_depth
      (by simpa only [p, msg, h64, h32, h2adr] using henter)
      (by simpa only [p, msg, h64, h32] using hres)
  simpa only [p, msg, cev, child, post] using hrun

/-- Changing an account balance leaves every account's storage untouched. -/
lemma State.setBal_get_stor_direct
    (st : State) (changed queried : Adr) (value : B256) :
    ((st.setBal changed value).get queried).stor =
      (st.get queried).stor := by
  unfold State.setBal
  by_cases h : changed = queried
  · subst queried
    rw [State.get_set_self]
    rfl
  · rw [State.get_set_ne st h]

/-- The debit/credit preparation of a call changes balances only, including
the representation-normalizing zero-value case. -/
lemma State.subBal_addBal_get_stor
    {st mid : State} {src dst a : Adr} {value : B256}
    (hsub : st.subBal src value = some mid) :
    ((mid.addBal dst value).get a).stor = (st.get a).stor := by
  unfold State.subBal at hsub
  split at hsub
  · contradiction
  · injection hsub with hmid
    subst mid
    unfold State.addBal
    rw [State.setBal_get_stor_direct, State.setBal_get_stor_direct]

/-- A warm, undelegated address-two call over already-covered 64-byte input
and 32-byte output windows succeeds with the exact SHA-256 image.  The net
instruction cost is 184 gas: 100 for the warm account access and 84 for the
two-word precompile input. -/
theorem Ninst.runCompiled_statcall_sha256_64_warm
    {sevm : Sevm} {devm : Devm} {iiw oiw : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: (2 : B256) :: iiw :: (64 : B256) ::
        oiw :: (32 : B256) :: s)
    (hgas : devm.gasLeft = G)
    (hcovered : memExtsSize devm.memory.size
      [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = devm.memory.size)
    (hnodeleg : getDelegatedCodeAddress (devm.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ devm.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hfloor : 185 ≤ G)
    (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .statcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = devm.memory.write oiw.toNat
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes ∧
      post.gasLeft = G - 184 ∧
      post.returnData =
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor devm a) ∧
      post.logs = devm.logs ∧
      post.output = devm.output ∧
      post.error = devm.error ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal 2 0 := by
  let base := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩
  have hext : base.extCost
      [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = 0 := by
    exact Devm.extCost_covered hcovered
  have hnodel :
      getDelegatedCodeAddress (base.state.getCode 2) = none := by
    change getDelegatedCodeAddress (devm.getCode 2) = none
    exact hnodeleg
  let d0 := addAccessedAddress base 2
  have hdel : accessDelegation d0 2 =
      ⟨false, 2, base.state.getCode 2, 0, d0⟩ := by
    dsimp only [d0]
    unfold accessDelegation
    simp only [show (addAccessedAddress base 2).state.getCode 2 =
      base.state.getCode 2 from rfl, hnodel]
  have hd0gas : d0.gasLeft = G := by
    change devm.gasLeft = G
    exact hgas
  have hacc : accessCost 2 base.accessedAddresses + 0 =
      gasWarmAccess := by
    change accessCost 2 devm.accessedAddresses + 0 = gasWarmAccess
    unfold accessCost
    rw [if_pos hwarm]
    omega
  obtain ⟨mcc, mcs, hsplit⟩ : ∃ mcc mcs,
      calculateMsgCallGas 0 (Nat.toB256 G).toNat d0.gasLeft
        0 gasWarmAccess = ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs, hcross, hgasout⟩ :
      84 ≤ mcs ∧ mcc + 0 ≤ G ∧
        G - (mcc + 0) + (mcs - 84) = G - 184 := by
    have hGnat : (Nat.toB256 G).toNat = G :=
      B256.toNat_toB256_of_lt hbound
    rw [hd0gas] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, if_neg (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin :
        min G (except64th (G - 0 - 100)) =
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
  let p := callSpawnParent d0 (mcc + 0)
    iiw.toNat 64 oiw.toNat 32
  let msg := statcallSpawnMsg sevm p mcs 2 2
    iiw.toNat 64 (base.state.getCode 2) false
  have hafford : ¬ msg.benv.state.bal msg.caller < msg.value := by
    change ¬ (d0.getAcct sevm.currentTarget).bal < 0
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _)
  obtain ⟨stmid, hsub, hbt⟩ :=
    Msg.benvAfterTransfer_of_affordable msg rfl hafford
  let benv' := (msg.benv.withState stmid).addBal
    msg.currentTarget msg.value
  have hpre' :
      (!((msg.withBenv benv').disablePrecompiles) &&
        decide ((msg.withBenv benv').benv.stat.rules.isPrecomp 2)) = true := by
    change decide (sevm.benvStat.rules.isPrecomp 2) = true
    exact hpre
  have hlen : (initEvm (msg.withBenv benv')).sta.data.length = 64 := by
    change (p.memory.data.sliceD iiw.toNat 64 0).length = 64
    rw [Array.sliceD_eq_map, List.length_map, List.length_range]
  have hproom : p.stack.length < 1024 := by
    change s.length < 1024
    exact hroom
  let cev := initEvm (msg.withBenv benv')
  let child :=
    (cev.dyna.withGasLeft (cev.dyna.gasLeft - 84)).withOutput
      (Bytes.sha256 cev.sta.data).toBytes
  let post :=
    (((incorporateChildOnSuccess p child child.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft⟩).memWrite
        oiw.toNat (child.output.take 32))
  have hrun : Ninst.RunCompiled sevm devm (.exec .statcall) post := by
    simpa only [msg, cev, child, post] using
      (Ninst.runCompiled_statcall_sha256_64
        (parent := p) (benv := benv') hstk hext hdel hacc hsplit
        (by rw [hd0gas]; exact hcross) hdepth rfl hbt hpre' hlen hmcs hproom)
  have hpmem : p.memory = devm.memory := by
    change d0.memory.extends
      [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = devm.memory
    change devm.memory.extends
      [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = devm.memory
    exact Mem.extends_covered hcovered
  have hcevdata :
      cev.sta.data = devm.memory.data.sliceD iiw.toNat 64 0 := by
    change p.memory.data.sliceD iiw.toNat 64 0 =
      devm.memory.data.sliceD iiw.toNat 64 0
    rw [hpmem]
  have hchildOutput :
      child.output =
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes := by
    change (Bytes.sha256 cev.sta.data).toBytes = _
    rw [hcevdata]
  have hchildGas : child.gasLeft = mcs - 84 := by
    rfl
  have hchildLogs : child.logs = [] := by
    rfl
  have hsub' :
      devm.state.subBal sevm.currentTarget 0 = some stmid := by
    have hp : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, statcallSpawnMsg, callMsg] using hsub
    exact hp
  have hchildState : child.state = stmid.addBal 2 0 := by
    rfl
  have hstackPost : post.stack = 1 :: s := by
    change 1 :: p.stack = 1 :: s
    rfl
  have htake :
      ((Bytes.sha256
        (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes).take 32 =
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes := by
    rw [← B256.length_toBytes
      (Bytes.sha256 (devm.memory.data.sliceD iiw.toNat 64 0)),
      List.take_length]
  have hmemoryPost :
      post.memory = devm.memory.write oiw.toNat
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes := by
    change p.memory.write oiw.toNat (child.output.take 32) = _
    rw [hchildOutput, htake, hpmem]
  have hgasPost : post.gasLeft = G - 184 := by
    change p.gasLeft + child.gasLeft = G - 184
    rw [hchildGas]
    change d0.gasLeft - (mcc + 0) + (mcs - 84) = G - 184
    rw [hd0gas]
    exact hgasout
  have hreturnData :
      post.returnData =
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes := by
    change child.output = _
    exact hchildOutput
  have hstorage :
      ∀ a, Devm.getStor post a = Devm.getStor devm a := by
    intro a
    change (child.state.get a).stor = (devm.state.get a).stor
    rw [hchildState]
    exact State.subBal_addBal_get_stor hsub'
  have hlogsPost : post.logs = devm.logs := by
    change p.logs ++ child.logs = devm.logs
    rw [hchildLogs, List.append_nil]
    rfl
  have houtputPost : post.output = devm.output := by
    change p.output = devm.output
    rfl
  have herrorPost : post.error = devm.error := by
    change p.error = devm.error
    rfl
  have hstatePost : post.state = stmid.addBal 2 0 := by
    change child.state = stmid.addBal 2 0
    exact hchildState
  exact ⟨post, hrun, hstackPost, hmemoryPost, hgasPost, hreturnData,
    hstorage, hlogsPost, houtputPost, herrorPost,
    stmid, hsub', hstatePost⟩

end Blanc
