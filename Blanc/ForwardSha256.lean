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

/-- Assemble a successful, synchronously resolved 64-byte SHA-256 `STATICCALL`
from the generic call-frame pieces while preserving its empty child slot.
Arithmetic and delegation resolution remain explicit at this layer. -/
theorem Ninst.childlessRunCompiled_statcall_sha256_64
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
    Ninst.ChildlessRunCompiled sevm devm (.exec .statcall) post := by
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
  have hrun : Ninst.ChildlessRunCompiled sevm devm (.exec .statcall) post :=
    Ninst.childlessRunCompiled_statcall_doneFrame
      h_stk (by simpa only [h64, h32] using h_ext) h_del h_acc
      (by simpa using h_split) h_gas h_depth
      (by simpa only [p, msg, h64, h32, h2adr] using henter)
      (by simpa only [p, msg, h64, h32] using hres)
  simpa only [p, msg, cev, child, post] using hrun

/-- Ordinary compiled-step projection of
`childlessRunCompiled_statcall_sha256_64`. -/
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
  exact (Ninst.childlessRunCompiled_statcall_sha256_64
    h_stk h_ext h_del h_acc h_split h_gas h_depth h_parent h_bt h_pre
    h_len h_shaGas h_room).toRunCompiled

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

private lemma rawInsertIfNew_eq_self_of_contains
    {α : Type} {β : α → Type} [BEq α] [Hashable α]
    (m : Std.DHashMap.Internal.Raw₀ α β) (a : α) (b : β a)
    (h : Std.DHashMap.Internal.Raw₀.contains m a = true) :
    Std.DHashMap.Internal.Raw₀.insertIfNew m a b = m := by
  rcases m with ⟨⟨size, buckets⟩, hm⟩
  unfold Std.DHashMap.Internal.Raw₀.contains at h
  unfold Std.DHashMap.Internal.Raw₀.insertIfNew
  dsimp only at h ⊢
  split
  · rfl
  · contradiction

private lemma rawInsertListIfNew_eq_self_of_forall_contains
    {α : Type} {β : α → Type} [BEq α] [Hashable α]
    (m : Std.DHashMap.Internal.Raw₀ α β)
    (l : List ((a : α) × β a))
    (h : ∀ p ∈ l,
      Std.DHashMap.Internal.Raw₀.contains m p.1 = true) :
    Std.DHashMap.Internal.Raw₀.insertListIfNewₘ m l = m := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      rw [Std.DHashMap.Internal.Raw₀.insertListIfNewₘ,
        rawInsertIfNew_eq_self_of_contains m hd.1 hd.2
          (h hd (by simp))]
      exact ih (fun p hp => h p (by simp [hp]))

private lemma rawUnion_self
    {α : Type} {β : α → Type}
    [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : Std.DHashMap.Internal.Raw₀ α β)
    (hwf : Std.DHashMap.Internal.Raw.WFImp m.1) :
    Std.DHashMap.Internal.Raw₀.union m m = m := by
  unfold Std.DHashMap.Internal.Raw₀.union
  rw [if_pos (le_refl _)]
  rw [Std.DHashMap.Internal.Raw₀.insertManyIfNew_eq_insertListIfNewₘ_toListModel]
  apply rawInsertListIfNew_eq_self_of_forall_contains
  intro p hp
  rw [Std.DHashMap.Internal.Raw₀.contains_eq_containsKey hwf]
  exact Std.Internal.List.containsKey_of_mem hp

private lemma hashSet_union_self
    {α : Type} [BEq α] [Hashable α] [EquivBEq α]
    [LawfulHashable α] (m : Std.HashSet α) :
    m.union m = m := by
  rcases m with ⟨⟨⟨raw, wf⟩⟩⟩
  have hu := congrArg Subtype.val
    (rawUnion_self ⟨raw, wf.size_buckets_pos⟩
      (Std.DHashMap.Internal.Raw.WF.out wf))
  unfold Std.HashSet.union Std.HashMap.union Std.DHashMap.union
  congr 3

private lemma hashSet_insert_eq_self_of_mem
    {α : Type} [BEq α] [Hashable α]
    (m : Std.HashSet α) (a : α) (h : a ∈ m) :
    m.insert a = m := by
  rcases m with ⟨⟨⟨raw, wf⟩⟩⟩
  change Std.DHashMap.Internal.Raw₀.contains
    ⟨raw, wf.size_buckets_pos⟩ a = true at h
  have hi := congrArg Subtype.val
    (rawInsertIfNew_eq_self_of_contains
      ⟨raw, wf.size_buckets_pos⟩ a () h)
  simp only [Std.HashSet.insert, Std.HashMap.insertIfNew,
    Std.DHashMap.insertIfNew]
  congr 3

private lemma addAccessedAddress_accessedAddresses_eq_of_mem
    {d : Devm} {a : Adr} (h : a ∈ d.accessedAddresses) :
    (addAccessedAddress d a).accessedAddresses =
      d.accessedAddresses := by
  change d.accessedAddresses.insert a = d.accessedAddresses
  exact hashSet_insert_eq_self_of_mem _ _ h

/-- A call's zero-value debit/credit preparation preserves all code. -/
lemma State.subBal_addBal_getCode
    {st mid : State} {src dst a : Adr} {value : B256}
    (hsub : st.subBal src value = some mid) :
    (mid.addBal dst value).getCode a = st.getCode a := by
  rw [State.addBal_getCode, State.subBal_getCode hsub]

private lemma successfulCallPost_accessedAddresses
    {parent child : Devm} {returnData bytes : Bytes}
    {mach : Mach} {offset : Nat}
    (h : child.accessedAddresses = parent.accessedAddresses) :
    (((incorporateChildOnSuccess parent child returnData).setMach mach).memWrite
      offset bytes).accessedAddresses = parent.accessedAddresses := by
  change parent.accessedAddresses.union child.accessedAddresses =
    parent.accessedAddresses
  rw [h, hashSet_union_self]

private lemma successfulCallPost_accessedStorageKeys
    {parent child : Devm} {returnData bytes : Bytes}
    {mach : Mach} {offset : Nat}
    (h : child.accessedStorageKeys = parent.accessedStorageKeys) :
    (((incorporateChildOnSuccess parent child returnData).setMach mach).memWrite
      offset bytes).accessedStorageKeys = parent.accessedStorageKeys := by
  change parent.accessedStorageKeys.union child.accessedStorageKeys =
    parent.accessedStorageKeys
  rw [h, hashSet_union_self]

private lemma successfulCallPost_getCode
    {pre parent child : Devm} {returnData bytes : Bytes}
    {mach : Mach} {offset : Nat}
    (h : ∀ a, child.getCode a = pre.getCode a) :
    ∀ a,
      (((incorporateChildOnSuccess parent child returnData).setMach mach).memWrite
        offset bytes).getCode a = pre.getCode a := by
  intro a
  change child.getCode a = pre.getCode a
  exact h a

/-- A warm, undelegated address-two call over a 64-byte input and 32-byte
output window succeeds with the exact SHA-256 image.  The net instruction
cost is 184 gas plus the selected memory-expansion charge: 100 for the warm
account access and 84 for the two-word precompile input. -/
theorem Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext_full
    {sevm : Sevm} {devm : Devm} {iiw oiw : B256}
    {s : List B256} {G ext : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: (2 : B256) :: iiw :: (64 : B256) ::
        oiw :: (32 : B256) :: s)
    (hgas : devm.gasLeft = G)
    (hext : (devm.setMach
      ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = ext)
    (hnodeleg : getDelegatedCodeAddress (devm.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ devm.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hfloor : 185 + ext ≤ G)
    (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.ChildlessRunCompiled sevm devm (.exec .statcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩]).write oiw.toNat
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes ∧
      post.gasLeft = G - (184 + ext) ∧
      post.returnData =
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor devm a) ∧
      (∀ a, post.getCode a = devm.getCode a) ∧
      post.accessedAddresses = devm.accessedAddresses ∧
      post.accessedStorageKeys = devm.accessedStorageKeys ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.output = devm.output ∧
      post.error = devm.error ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal 2 0 := by
  let base := devm.setMach ⟨s, devm.memory, devm.gasLeft⟩
  have hextBase : base.extCost
      [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = ext := by
    simpa only [base] using hext
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
        ext gasWarmAccess = ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs, hcross, hgasout⟩ :
      84 ≤ mcs ∧ mcc + ext ≤ G ∧
        G - (mcc + ext) + (mcs - 84) = G - (184 + ext) := by
    have hGnat : (Nat.toB256 G).toNat = G :=
      B256.toNat_toB256_of_lt hbound
    rw [hd0gas] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, if_neg (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin :
        min G (except64th (G - ext - 100)) =
          except64th (G - ext - 100) := by
      have h1 : except64th (G - ext - 100) ≤ G := by
        unfold except64th
        omega
      rw [Nat.min_eq_right h1]
    rw [hmin] at hsplit
    have h1 : except64th (G - ext - 100) + 100 = mcc :=
      congrArg Prod.fst hsplit
    have h2 : except64th (G - ext - 100) + 0 = mcs :=
      congrArg Prod.snd hsplit
    unfold except64th at h1 h2
    exact ⟨by omega, by omega, by omega⟩
  let p := callSpawnParent d0 (mcc + ext)
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
  have hrun : Ninst.ChildlessRunCompiled sevm devm (.exec .statcall) post := by
    simpa only [msg, cev, child, post] using
      (Ninst.childlessRunCompiled_statcall_sha256_64
        (parent := p) (benv := benv') hstk hextBase hdel hacc hsplit
        (by rw [hd0gas]; exact hcross) hdepth rfl hbt hpre' hlen hmcs hproom)
  have hpmem : p.memory = devm.memory.extends
      [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] := by
    rfl
  have hcevdata :
      cev.sta.data = devm.memory.data.sliceD iiw.toNat 64 0 := by
    change p.memory.data.sliceD iiw.toNat 64 0 =
      devm.memory.data.sliceD iiw.toNat 64 0
    rw [hpmem]
    rfl
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
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩]).write oiw.toNat
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes := by
    change p.memory.write oiw.toNat (child.output.take 32) = _
    rw [hchildOutput, htake, hpmem]
  have hgasPost : post.gasLeft = G - (184 + ext) := by
    change p.gasLeft + child.gasLeft = G - (184 + ext)
    rw [hchildGas]
    change d0.gasLeft - (mcc + ext) + (mcs - 84) = G - (184 + ext)
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
  have hchildCode : ∀ a, child.getCode a = devm.getCode a := by
    intro a
    change (stmid.addBal 2 0).getCode a = devm.state.getCode a
    exact State.subBal_addBal_getCode hsub'
  have hcode : ∀ a, post.getCode a = devm.getCode a := by
    simpa only [post] using
      (successfulCallPost_getCode
        (parent := p) (child := child)
        (returnData := child.output)
        (mach := ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft⟩)
        (offset := oiw.toNat) (bytes := child.output.take 32) hchildCode)
  have hpAddresses : p.accessedAddresses = devm.accessedAddresses := by
    change d0.accessedAddresses = devm.accessedAddresses
    calc
      d0.accessedAddresses = base.accessedAddresses := by
        apply addAccessedAddress_accessedAddresses_eq_of_mem
        change (2 : Adr) ∈ devm.accessedAddresses
        exact hwarm
      _ = devm.accessedAddresses := rfl
  have hchildAddresses : child.accessedAddresses = p.accessedAddresses := rfl
  have hpostParentAddresses :
      post.accessedAddresses = p.accessedAddresses := by
    simpa only [post] using
      (successfulCallPost_accessedAddresses
        (parent := p) (child := child) (returnData := child.output)
        (mach := ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft⟩)
        (offset := oiw.toNat) (bytes := child.output.take 32)
        hchildAddresses)
  have haddresses : post.accessedAddresses = devm.accessedAddresses :=
    hpostParentAddresses.trans hpAddresses
  have hpKeys : p.accessedStorageKeys = devm.accessedStorageKeys := rfl
  have hchildKeys : child.accessedStorageKeys = p.accessedStorageKeys := rfl
  have hpostParentKeys :
      post.accessedStorageKeys = p.accessedStorageKeys := by
    simpa only [post] using
      (successfulCallPost_accessedStorageKeys
        (parent := p) (child := child) (returnData := child.output)
        (mach := ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft⟩)
        (offset := oiw.toNat) (bytes := child.output.take 32) hchildKeys)
  have hkeys : post.accessedStorageKeys = devm.accessedStorageKeys :=
    hpostParentKeys.trans hpKeys
  have hlogsPost : post.logs = devm.logs := by
    change p.logs ++ child.logs = devm.logs
    rw [hchildLogs, List.append_nil]
    rfl
  have hrefundPost : post.refundCounter = devm.refundCounter := by
    dsimp only [post, child, cev, initEvm, initDevm]
    change p.refundCounter + 0 = devm.refundCounter
    rw [show p.refundCounter = devm.refundCounter from rfl]
    simp
  have hdeletePost :
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty := by
    dsimp only [post, child, cev, initEvm, initDevm]
    change (p.accountsToDelete.union
      Std.HashSet.emptyWithCapacity).isEmpty =
        devm.accountsToDelete.isEmpty
    rw [show p.accountsToDelete = devm.accountsToDelete from rfl]
    simp
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
    hstorage, hcode, haddresses, hkeys,
    hlogsPost, hrefundPost, hdeletePost, houtputPost, herrorPost,
    stmid, hsub', hstatePost⟩

/-- Compatibility projection of the full warm SHA-256 crossing.  Consumers
that must settle a transaction should use the `_full` theorem so refund and
account-deletion preservation remain explicit. -/
theorem Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext
    {sevm : Sevm} {devm : Devm} {iiw oiw : B256}
    {s : List B256} {G ext : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: (2 : B256) :: iiw :: (64 : B256) ::
        oiw :: (32 : B256) :: s)
    (hgas : devm.gasLeft = G)
    (hext : (devm.setMach
      ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = ext)
    (hnodeleg : getDelegatedCodeAddress (devm.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ devm.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hfloor : 185 + ext ≤ G)
    (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.ChildlessRunCompiled sevm devm (.exec .statcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩]).write oiw.toNat
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes ∧
      post.gasLeft = G - (184 + ext) ∧
      post.returnData =
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor devm a) ∧
      (∀ a, post.getCode a = devm.getCode a) ∧
      post.accessedAddresses = devm.accessedAddresses ∧
      post.accessedStorageKeys = devm.accessedStorageKeys ∧
      post.logs = devm.logs ∧
      post.output = devm.output ∧
      post.error = devm.error ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal 2 0 := by
  obtain ⟨post, hrun, hstack, hmemory, hgas', hreturn, hstorage,
      hcode, haddresses, hkeys, hlogs, _hrefund, _hdelete, houtput,
      herror, stmid, hsub, hstate⟩ :=
    Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext_full
      hstk hgas hext hnodeleg hwarm hpre hdepth hfloor hbound hroom
  exact ⟨post, hrun, hstack, hmemory, hgas', hreturn, hstorage, hcode,
    haddresses, hkeys, hlogs, houtput, herror, stmid, hsub, hstate⟩

/-- Ordinary compiled-step projection of the childless warm SHA-256 call.
All state and gas facts are identical; only the empty child-slot fact is
forgotten. -/
theorem Ninst.runCompiled_statcall_sha256_64_warm_ext
    {sevm : Sevm} {devm : Devm} {iiw oiw : B256}
    {s : List B256} {G ext : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: (2 : B256) :: iiw :: (64 : B256) ::
        oiw :: (32 : B256) :: s)
    (hgas : devm.gasLeft = G)
    (hext : (devm.setMach
      ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = ext)
    (hnodeleg : getDelegatedCodeAddress (devm.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ devm.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hfloor : 185 + ext ≤ G)
    (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .statcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩]).write oiw.toNat
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes ∧
      post.gasLeft = G - (184 + ext) ∧
      post.returnData =
        (Bytes.sha256
          (devm.memory.data.sliceD iiw.toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor devm a) ∧
      (∀ a, post.getCode a = devm.getCode a) ∧
      post.accessedAddresses = devm.accessedAddresses ∧
      post.accessedStorageKeys = devm.accessedStorageKeys ∧
      post.logs = devm.logs ∧
      post.output = devm.output ∧
      post.error = devm.error ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal 2 0 := by
  obtain ⟨post, hrun, hstack, hmemory, hgas', hreturn,
      hstorage, hcode, haddresses, hkeys, hlogs, houtput, herror,
      stmid, hsub, hstate⟩ :=
    Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext
      hstk hgas hext hnodeleg hwarm hpre hdepth hfloor hbound hroom
  exact ⟨post, hrun.toRunCompiled, hstack, hmemory, hgas', hreturn,
    hstorage, hcode, haddresses, hkeys, hlogs, houtput, herror,
    stmid, hsub, hstate⟩

/-- Covered-memory compatibility form of
`runCompiled_statcall_sha256_64_warm_ext`. -/
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
      (∀ a, post.getCode a = devm.getCode a) ∧
      post.accessedAddresses = devm.accessedAddresses ∧
      post.accessedStorageKeys = devm.accessedStorageKeys ∧
      post.logs = devm.logs ∧
      post.output = devm.output ∧
      post.error = devm.error ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal 2 0 := by
  have hext : (devm.setMach
      ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = 0 :=
    Devm.extCost_covered hcovered
  simpa only [Nat.add_zero, Mem.extends_covered hcovered] using
    (Ninst.runCompiled_statcall_sha256_64_warm_ext
      (ext := 0) hstk hgas hext hnodeleg hwarm hpre hdepth
      (by omega) hbound hroom)

end Blanc
