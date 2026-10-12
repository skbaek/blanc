import Blanc.ForwardSha256
import Blanc.ForwardLog

/-!
# Beacon deposit re-pin bridge (unit-local, hoisting candidate)

Jaune `ca9f27d` prices SSTORE from the machine read `Devm.getOrigStorVal`,
which consults `createdAccounts`.  Transporting an exact SSTORE price across
the warm SHA-256 precompile crossing therefore needs the created-account set
of the crossing's poststate.  The core producer
`Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext_full` constructs its
poststate explicitly but does not expose that set; this companion re-derives
the same crossing with the extra conjunct.  It is a hoisting candidate for
`Blanc/ForwardSha256.lean` (as an added conjunct of the core producer).
-/

namespace Blanc.BeaconDeposit.RepinBridge

open Jaune Blanc

private lemma addAccessedAddress_accessedAddresses_eq_of_mem
    {d : Devm} {a : Adr} (h : a ∈ d.accessedAddresses) :
    (addAccessedAddress d a).accessedAddresses =
      d.accessedAddresses := by
  change d.accessedAddresses.insert a = d.accessedAddresses
  exact hashSet_insert_eq_self_of_mem _ _ h

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

/-- `Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext_full` with the
created-account set of the explicit poststate exposed. -/
theorem childlessRunCompiled_staticcall_sha256_64_warm_ext_created
    {sevm : Sevm} {devm : Devm} {iiw oiw : B256}
    {s : List B256} {G ext : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: (2 : B256) :: iiw :: (64 : B256) ::
        oiw :: (32 : B256) :: s)
    (hgas : devm.gasLeft = G)
    (hext : (devm.setMach
      ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩).extCost
        [⟨iiw.toNat, 64⟩, ⟨oiw.toNat, 32⟩] = ext)
    (hnodeleg : getDelegatedCodeAddress (devm.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ devm.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdepth : sevm.depth ≠ 0)
    (hfloor : 185 + ext ≤ G)
    (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.ChildlessRunCompiled sevm devm (.exec .staticcall) post ∧
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
      post.state = devm.state ∧
      post.createdAccounts = devm.createdAccounts := by
  let base := devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩
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
  let msg := staticcallSpawnMsg sevm p mcs 2 2
    iiw.toNat 64 (base.state.getCode 2) false
  have hbt : msg.benvAfterTransfer = .ok msg.benv :=
    Msg.benvAfterTransfer_of_value_zero rfl
  let benv' := msg.benv
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
      ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft, p.stateGas⟩).memWrite
        oiw.toNat (child.output.take 32))
  have hrun : Ninst.ChildlessRunCompiled sevm devm (.exec .staticcall) post := by
    simpa only [msg, cev, child, post] using
      (Ninst.childlessRunCompiled_staticcall_sha256_64
        (parent := p) (benv := benv') hstk hextBase hdel hacc hsplit
        (by rw [hd0gas]; exact hcross) hfork hdepth rfl hbt hpre' hlen hmcs hproom)
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
  have hstateGas : benv'.stat.rules.stateGas = none := by
    change sevm.benvStat.rules.stateGas = none
    exact hfork.rules_stateGas_none
  have hchildLogs : child.logs = [] := by
    change cev.dyna.logs = []
    dsimp only [cev, initEvm, initDevm, Msg.withBenv_gas, Msg.withBenv_stat_rules]
    rw [hstateGas]
    rfl
  have hchildState : child.state = devm.state := by
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
  have hchildCode : ∀ a, child.getCode a = devm.getCode a := by
    intro a
    change child.state.getCode a = devm.state.getCode a
    rw [hchildState]
  have hcode : ∀ a, post.getCode a = devm.getCode a := by
    simpa only [post] using
      (successfulCallPost_getCode
        (parent := p) (child := child)
        (returnData := child.output)
        (mach := ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft, p.stateGas⟩)
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
        (mach := ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft, p.stateGas⟩)
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
        (mach := ⟨1 :: p.stack, p.memory, p.gasLeft + child.gasLeft, p.stateGas⟩)
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
    simp only [add_zero]
  have hdeletePost :
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty := by
    dsimp only [post, child, cev, initEvm, initDevm]
    change (p.accountsToDelete.union
      Std.HashSet.emptyWithCapacity).isEmpty =
        devm.accountsToDelete.isEmpty
    rw [show p.accountsToDelete = devm.accountsToDelete from rfl]
    simp only [Std.HashSet.union_eq, Std.HashSet.isEmpty_union,
      Std.HashSet.isEmpty_emptyWithCapacity, Bool.and_true]
  have houtputPost : post.output = devm.output := by
    change p.output = devm.output
    rfl
  have herrorPost : post.error = devm.error := by
    change p.error = devm.error
    rfl
  have hcreatedPost : post.createdAccounts = devm.createdAccounts := by
    rfl
  have hstatePost : post.state = devm.state := by
    change child.state = devm.state
    exact hchildState
  exact ⟨post, hrun, hstackPost, hmemoryPost, hgasPost, hreturnData,
    hstorage, hcode, haddresses, hkeys,
    hlogsPost, hrefundPost, hdeletePost, houtputPost, herrorPost,
    hstatePost, hcreatedPost⟩

/-- A selected `SLOAD` leaves the created-account set unchanged. -/
theorem afterSload_createdAccounts
    (sevm : Sevm) (base : Devm) (key : B256) :
    (afterSload sevm base key).createdAccounts = base.createdAccounts := by
  unfold afterSload
  split <;> rfl

/-- A selected `SSTORE` leaves the created-account set unchanged. -/
theorem afterSstore_createdAccounts
    (sevm : Sevm) (devm : Devm) (key value : B256) :
    (afterSstore sevm devm key value).createdAccounts =
      devm.createdAccounts := by
  unfold afterSstore
  split <;> rfl

/-- The machine original read agrees between two machines with the same
created-account set. -/
theorem getOrigStorVal_congr_created
    {sevm : Sevm} {d1 d2 : Devm} (adr : Adr) (key : B256)
    (hcreated : d1.createdAccounts = d2.createdAccounts) :
    d1.getOrigStorVal sevm adr key = d2.getOrigStorVal sevm adr key := by
  unfold Devm.getOrigStorVal
  rw [hcreated]

/-- `Func.runCompiledTo_log_step_exists` with the created-account set of the
exhibited post-log state exposed. -/
lemma runCompiledTo_log_step_exists_created {fs : List Func} {sevm : Sevm}
    {devm : Devm}
    {n : Fin 5} {i sz : B256} {topics s : List B256} {c G : Nat} {M M' : Mem}
    {payload : Bytes} {rest : Func}
    (h_stk : devm.stack = i :: sz :: (topics ++ s))
    (h_len : topics.length = n.val) (h_static : sevm.isStatic = false)
    (h_mem : devm.memory = M)
    (h_cost : gLog + gLogdata * sz.toNat + gLogtopic * n.val
      + devm.extCost [⟨i.toNat, sz.toNat⟩] = c)
    (h_data : (M.read i.toNat sz.toNat).1 = payload)
    (h_img : (M.read i.toNat sz.toNat).2 = M')
    (h_gas : devm.gasLeft = G + c) :
    ∃ logged : Devm,
      logged.logs = devm.logs ++ [⟨sevm.currentTarget, topics, payload⟩] ∧
      (∀ (a : Adr) (k : B256), logged.getStorVal a k = devm.getStorVal a k) ∧
      (∀ a : Adr, Devm.getStor logged a = Devm.getStor devm a) ∧
      (∀ a : Adr, logged.getBal a = devm.getBal a) ∧
      (∀ a : Adr, logged.getCode a = devm.getCode a) ∧
      logged.accessedStorageKeys = devm.accessedStorageKeys ∧
      logged.accessedAddresses = devm.accessedAddresses ∧
      logged.output = devm.output ∧
      logged.error = devm.error ∧
      logged.createdAccounts = devm.createdAccounts ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm (logged.setMach ⟨s, M', G, logged.stateGas⟩) rest ex →
        Func.RunCompiledTo fs sevm devm (Func.next (.reg (.log n)) rest) ex := by
  refine ⟨devm.addLog ⟨sevm.currentTarget, topics, payload⟩, rfl,
    fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl,
    rfl, rfl, rfl, ?_⟩
  intro ex htail
  subst h_mem
  exact Func.RunCompiledTo.next
    (Ninst.runCompiled_log_of (G := G) h_stk h_len h_static h_cost h_data
      h_img (by omega)) htail

end Blanc.BeaconDeposit.RepinBridge
