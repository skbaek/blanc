import Blanc.LidoCircuitBreakerPauseWalk
import Blanc.LidoCircuitBreakerPauseWorld

/-!
The `.ok`-flavour walk legs of `pauseAfterSet`, through both external calls.

`Blanc/LidoCircuitBreakerPauseWalk.lean` carries the pause route's `.ok` walk
legs up to the boundaries the register side owns; what it cannot supply is the
far side of `pauseAfterSet`'s two external calls.
`Blanc/LidoCircuitBreakerPauseWorld.lean` supplies the responder callee and the
two compiled-instruction crossings through it.  This leaf composes them: from
`pauseAfterSet`'s entry, through the target-code guard, the `pauseFor` `CALL`,
the `isPaused()` `STATICCALL` and the decode, to the `pauseSuccess` boundary —
and from `pauseSuccess` to `Func.stop`.

The factoring at the `pauseSuccess` boundary is load-bearing: the join theorem
applies `pauseSuccess_expiryWrite_dichotomy` to the sub-walk entered there, so
the two legs are separate lemmas composable at exactly that point.  The
`pauseAfterSet` leg hands its continuation an *arbitrary* state pinned by
projection facts — the crossing lemmas expose their post-states existentially,
so the boundary state has no closed term — and the `pauseSuccess` legs are
stated over an arbitrary `base` so the join can enter them at that state.

Costs follow the register-side conventions: fixed charges are exact numerals,
warmth-dependent charges are hypothesis-supplied numerals
(`temporalSloadCost`/`temporalAccountAccessCost` equations), and `SSTORE`
charges are hypothesis-supplied `sstoreValueCost` numerals in the style of
`afterOldPauser_finishSetPauser_runCompiled`.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Small helpers -/

/-- The checked-addition flag of a non-wrapping heartbeat sum: with
`time + interval` inside `2 ^ 256`, the source's `LT` overflow probe answers
zero. -/
private lemma ltCheck_checkedSum_eq_zero {time interval : B256}
    (hnof : B256.Nof time interval) :
    ((interval + time) <? time) = 0 := by
  have hnof' : B256.Nof interval time := by
    unfold B256.Nof at hnof ⊢
    omega
  rw [B256.ltCheck, if_neg]
  intro hlt
  rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_add_eq_of_nof _ _ hnof'] at hlt
  omega

private theorem addAccessedAddress_setMach_setMach
    {base : Devm} {a : Adr} {m m' : Mach} :
    (addAccessedAddress (base.setMach m) a).setMach m' =
      (addAccessedAddress base a).setMach m' := rfl

/-! ## Temporal account access

`EXTCODESIZE`'s charge is warmth-dependent, and warmth is a fact about the
frame.  Mirror the `temporalSloadBase`/`temporalSloadCost` convention: the
caller supplies the charge as an equation about the entry world, and the walk
threads the possibly-warmed successor world. -/

/-- The world after an account access: unchanged when the address was warm,
warmed otherwise. -/
def temporalAccountAccessBase (base : Devm) (a : Adr) : Devm :=
  if a ∈ base.accessedAddresses then base else addAccessedAddress base a

/-- The warmth-dependent account-access charge. -/
def temporalAccountAccessCost (base : Devm) (a : Adr) : Nat :=
  if a ∈ base.accessedAddresses then gasWarmAccess else gasColdAccountAccess

theorem temporalAccountAccessBase_warm (base : Devm) (a : Adr) :
    a ∈ (temporalAccountAccessBase base a).accessedAddresses := by
  unfold temporalAccountAccessBase
  split <;> rename_i h
  · exact h
  · exact Std.HashSet.mem_insert_self

theorem temporalAccountAccessBase_mem (base : Devm) (a x : Adr) :
    x ∈ (temporalAccountAccessBase base a).accessedAddresses ↔
      (x = a ∨ x ∈ base.accessedAddresses) := by
  unfold temporalAccountAccessBase
  split <;> rename_i h
  · exact ⟨Or.inr, fun hx => hx.elim (fun he => he ▸ h) id⟩
  · constructor
    · intro hx
      rcases Std.HashSet.mem_insert.mp hx with he | hx'
      · exact Or.inl (eq_of_beq he).symm
      · exact Or.inr hx'
    · intro hx
      rcases hx with he | hx'
      · exact he ▸ Std.HashSet.mem_insert_self
      · exact Std.HashSet.mem_insert.mpr (Or.inr hx')

theorem temporalAccountAccessBase_state (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).state = base.state := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem temporalAccountAccessBase_getCode (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem temporalAccountAccessBase_error (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).error = base.error := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem temporalAccountAccessBase_output (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).output = base.output := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem temporalAccountAccessBase_logs (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).logs = base.logs := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem temporalAccountAccessBase_refundCounter (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).refundCounter = base.refundCounter := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem temporalAccountAccessBase_accountsToDelete (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).accountsToDelete =
      base.accountsToDelete := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem temporalAccountAccessBase_transientStorage (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).transientStorage =
      base.transientStorage := by
  unfold temporalAccountAccessBase
  split <;> rfl

theorem temporalAccountAccessBase_accessedStorageKeys (base : Devm) (a : Adr) :
    (temporalAccountAccessBase base a).accessedStorageKeys =
      base.accessedStorageKeys := by
  unfold temporalAccountAccessBase
  split <;> rfl

/-- Exact `EXTCODESIZE` step in the temporal convention: the charge is the
entry world's `temporalAccountAccessCost`, and the successor world is its
`temporalAccountAccessBase`. -/
theorem temporal_extcodesize_runCompiled
    {sevm : Sevm} {base : Devm} {x v : B256}
    {stack : List B256} {M : Mem} {G : Nat}
    (hval : (base.getCode x.toAdr).size.toB256 = v)
    (hroom : stack.length < 1024) :
    Ninst.RunCompiled sevm
      (base.setMach ⟨x :: stack, M,
        G + temporalAccountAccessCost base x.toAdr⟩)
      Ninst.extcodesize
      ((temporalAccountAccessBase base x.toAdr).setMach ⟨v :: stack, M, G⟩) := by
  by_cases hwarm : x.toAdr ∈ base.accessedAddresses
  · simp only [temporalAccountAccessBase, temporalAccountAccessCost,
      if_pos hwarm]
    simpa only [Devm.setMach_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_extcodesize_warm
        (devm := base.setMach ⟨x :: stack, M, G + gasWarmAccess⟩)
        rfl hwarm hval (by simp only [Devm.gasLeft_setMach]) hroom
  · simp only [temporalAccountAccessBase, temporalAccountAccessCost,
      if_neg hwarm]
    simpa only [addAccessedAddress_setMach_setMach, Devm.memory_setMach] using
      Ninst.runCompiled_extcodesize_cold
        (devm := base.setMach ⟨x :: stack, M, G + gasColdAccountAccess⟩)
        rfl hwarm hval (by simp only [Devm.gasLeft_setMach]) hroom

/-! ## The two crossings, resolved at a warm code-carrying callee

`runCompiled_call_zero_value_responder` and `runCompiled_statcall_responder`
take the delegation resolution, the access charge and the EIP-150 split as
premises because they are facts about the state *at the instruction*.  That
state is reachable here only through the first crossing's existential
post-state, so no caller of this module could state those premises.  These two
wrappers resolve them internally from facts a caller can state: the callee
account carries `calleeCode` (not a delegation designator, so the resolution
is the identity with charge `0`), the callee address is already warm (the
target-code guard read it), and the forwarded word is the frame's whole gas
account, so the EIP-150 `min` collapses and the crossing costs exactly
`117 = gasWarmAccess + 17` on top of what the callee retains. -/

private lemma responder_call_crossing
    {sevm : Sevm} {devm : Devm} {target iiw isw oiw osw : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: target :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (hgas : devm.gasLeft = G)
    (hext : devm.extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0)
    (hcode : devm.getCode target.toAdr = calleeCode)
    (hwarm : target.toAdr ∈ devm.accessedAddresses)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hfloor : 118 ≤ G) (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = G - 117 ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ devm.accessedAddresses) ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal target.toAdr 0 := by
  have hnodel : getDelegatedCodeAddress
      ((devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr) = none := by
    rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = devm.getCode target.toAdr from rfl, hcode]
    decide
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
  set d0 := addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
    target.toAdr with hd0
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
      calculateMsgCallGas 0 (Nat.toB256 G).toNat d0.gasLeft 0 gasWarmAccess =
        ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs17, hcross, hgasout⟩ :
      17 ≤ mcs ∧ mcc + 0 ≤ G ∧ G - (mcc + 0) + (mcs - 17) = G - 117 := by
    have hGnat : (Nat.toB256 G).toNat = G := B256.toNat_toB256_of_lt hbound
    rw [hd0gas] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, if_neg (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin : min G (except64th (G - 0 - 100)) = except64th (G - 100) := by
      have h1 : except64th (G - 0 - 100) ≤ G := by
        unfold except64th; omega
      rw [Nat.min_eq_right h1]
      norm_num
    rw [hmin] at hsplit
    have h1 : except64th (G - 100) + 100 = mcc := congrArg Prod.fst hsplit
    have h2 : except64th (G - 100) + 0 = mcs := congrArg Prod.snd hsplit
    unfold except64th at h1 h2
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨post, hrun, hstack, hmem, hgasl, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, haa, stmid, hsub, hstate⟩ :=
    runCompiled_call_zero_value_responder (gw := Nat.toB256 G) (cw := target)
      hstk (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0 from hext)
      hdel hacc hsplit (by rw [hd0gas]; exact hcross) hdepth hnp
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = calleeCode from hcode) hmcs17 hroom
  refine ⟨post, hrun, hstack, hmem, ?_, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, ?_, stmid, hsub, hstate⟩
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

private lemma responder_statcall_crossing
    {sevm : Sevm} {devm : Devm} {target iiw isw oiw osw : B256}
    {s : List B256} {G : Nat}
    (hstk : devm.stack =
      Nat.toB256 G :: target :: iiw :: isw :: oiw :: osw :: s)
    (hgas : devm.gasLeft = G)
    (hext : devm.extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0)
    (hcode : devm.getCode target.toAdr = calleeCode)
    (hwarm : target.toAdr ∈ devm.accessedAddresses)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hfloor : 118 ≤ G) (hbound : G < 2 ^ 256)
    (hroom : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .statcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = G - 117 ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ devm.accessedAddresses) ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal target.toAdr 0 := by
  have hnodel : getDelegatedCodeAddress
      ((devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr) = none := by
    rw [show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = devm.getCode target.toAdr from rfl, hcode]
    decide
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
  set d0 := addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
    target.toAdr with hd0
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
      calculateMsgCallGas 0 (Nat.toB256 G).toNat d0.gasLeft 0 gasWarmAccess =
        ⟨mcc, mcs⟩ := ⟨_, _, rfl⟩
  obtain ⟨hmcs17, hcross, hgasout⟩ :
      17 ≤ mcs ∧ mcc + 0 ≤ G ∧ G - (mcc + 0) + (mcs - 17) = G - 117 := by
    have hGnat : (Nat.toB256 G).toNat = G := B256.toNat_toB256_of_lt hbound
    rw [hd0gas] at hsplit
    unfold calculateMsgCallGas at hsplit
    rw [hGnat, if_neg (by simp only [gasWarmAccess]; omega)] at hsplit
    simp only [gasWarmAccess] at hsplit
    have hmin : min G (except64th (G - 0 - 100)) = except64th (G - 100) := by
      have h1 : except64th (G - 0 - 100) ≤ G := by
        unfold except64th; omega
      rw [Nat.min_eq_right h1]
      norm_num
    rw [hmin] at hsplit
    have h1 : except64th (G - 100) + 100 = mcc := congrArg Prod.fst hsplit
    have h2 : except64th (G - 100) + 0 = mcs := congrArg Prod.snd hsplit
    unfold except64th at h1 h2
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨post, hrun, hstack, hmem, hgasl, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, haa, stmid, hsub, hstate⟩ :=
    runCompiled_statcall_responder (gw := Nat.toB256 G) (tw := target)
      hstk (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = 0 from hext)
      hdel hacc hsplit (by rw [hd0gas]; exact hcross) hdepth hnp
      (show (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).state.getCode
        target.toAdr = calleeCode from hcode) hmcs17 hroom
  refine ⟨post, hrun, hstack, hmem, ?_, herr, hout, hret, hlogs, hrefund,
    hatd, htrans, hask, ?_, stmid, hsub, hstate⟩
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

/-! ## The shared expiry-write finish

Both `pauseSuccess` arms end in `pauseExpiryFinish` and differ only in the
word they carry into it. -/

set_option maxRecDepth 16384 in
set_option maxHeartbeats 800000 in
/-- `pauseExpiryFinish` from the carried expiry word: writes the word into the
caller's expiry cell (`SSTORE` charge supplied in the register-side
`sstoreValueCost` style), emits `HeartbeatUpdated(caller)` with the word as
payload, clears the reentrancy lock, and stops.  Charge `1512` plus the
store: `16` to the store key, `1396` from the store to the lock `TSTORE`,
`100` for the `TSTORE` itself. -/
theorem pauseExpiryFinish_ok_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (pauser value expiryCurrent expiryOriginal : B256)
    (storeCost G : Nat)
    (hsize : 32 ≤ M.size) (halign : M.size % 32 = 0)
    (hcaller : sevm.caller.toB256 = pauser)
    (hexpiry : base.getStorVal sevm.currentTarget (expirySlot pauser) =
      expiryCurrent)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot pauser) = expiryOriginal)
    (hwarmExpiry : (sevm.currentTarget, expirySlot pauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal expiryCurrent value =
      storeCost)
    (hstipend : gCallStipend < G + 1496 + storeCost)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[value], M, G + 1512 + storeCost⟩) pauseExpiryFinish
      ((((temporalSstorePost sevm base (expirySlot pauser) value).addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser],
            value.toBytes⟩).setMach
        ⟨[], M.write 0 value.toBytes, G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
  let storePost := temporalSstorePost sevm base (expirySlot pauser) value
  let hbLog : Log :=
    ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser], value.toBytes⟩
  let M' := M.write 0 value.toBytes
  have hvalueBytes : value.toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes value
    rw [h] at hlen
    simp at hlen
  have hsizeM' : M'.size = M.size :=
    Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using
        (show 0 + 32 ≤ M.size by omega))
  have halign' : M'.size % 32 = 0 := by rw [hsizeM']; exact halign
  have hzeroCovered' : 0 + 32 ≤ M'.size := by omega
  have hzeroRead' : (M'.read 0 32).1 = value.toBytes := by
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero M hvalueBytes)
  have hzeroMemory' : (M'.read 0 32).2 = M' := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hzeroCovered')]
  -- the lock `TSTORE` and the terminal `STOP`
  have htstoreStop : Func.RunCompiled fs sevm
      ((storePost.addLog hbLog).setMach ⟨[lockKey, 0], M', G + 100⟩)
      (Ninst.tstore ::: Func.stop)
      (((storePost.addLog hbLog).setMach ⟨[], M', G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
    refine Func.RunCompiled.next ?_ (Func.RunCompiled.last rfl)
    have h := runCompiled_tstore_of (sevm := sevm)
      (pre := (storePost.addLog hbLog).setMach ⟨[lockKey, 0], M', G + 100⟩)
      (key := lockKey) (value := 0) (stack := [])
      (G := G) rfl hstatic
      (by simp only [Devm.gasLeft_setMach, gasWarmAccess])
    simpa only [Devm.setMach_setMach, Devm.memory_setMach] using h
  -- the heartbeat event and the lock words
  have hlogTail : Func.RunCompiled fs sevm
      (storePost.setMach ⟨[], M', G + 1496⟩)
      (Ninst.caller ::: pushB256 heartbeatUpdatedEvent :::
        pushB256 (1 * 32) ::: pushB256 (0 * 32) ::: Ninst.log 2 :::
        pushB256 0 ::: pushB256 lockKey ::: Ninst.tstore ::: Func.stop)
      (((storePost.addLog hbLog).setMach ⟨[], M', G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
    func_run (7) [1381]
    case h_cost =>
      simp only [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((1 : B256) * 32).toNat = 32 by decide]
      rw [Devm.extCost_zero_of_le halign' hzeroCovered']
      norm_num [gLog, gLogdata, gLogtopic]
    case a =>
      simp only [show ((0 : B256) * 32).toNat = 0 by decide,
        show ((1 : B256) * 32).toNat = 32 by decide]
      rw [hzeroRead', hzeroMemory', hcaller]
      have hg : G + 1496 - 1396 = G + 100 := by omega
      rw [hg]
      exact htstoreStop
  -- the expiry `SSTORE`
  have hstore : Func.RunCompiled fs sevm
      (base.setMach ⟨[expirySlot pauser, value], M',
        G + 1496 + storeCost⟩)
      (Ninst.sstore ::: Ninst.caller :::
        pushB256 heartbeatUpdatedEvent :::
        pushB256 (1 * 32) ::: pushB256 (0 * 32) ::: Ninst.log 2 :::
        pushB256 0 ::: pushB256 lockKey ::: Ninst.tstore ::: Func.stop)
      (((storePost.addLog hbLog).setMach ⟨[], M', G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
    refine Func.RunCompiled.next
      (temporal_sstore_runCompiled hexpiry hexpiryOrig hstoreCost
        hwarmExpiry (by omega) hstatic) ?_
    exact hlogTail
  -- the store key and the scratch write
  show Func.RunCompiled fs sevm
    (base.setMach ⟨[value], M, G + 1512 + storeCost⟩)
    (Ninst.dup 0 ::: pushB256 (0 * 32) ::: Ninst.mstore :::
      Ninst.caller ::: pushB256 (regionWord expiryRegion) ::: Ninst.or :::
      Ninst.sstore ::: Ninst.caller ::: pushB256 heartbeatUpdatedEvent :::
      pushB256 (1 * 32) ::: pushB256 (0 * 32) ::: Ninst.log 2 :::
      pushB256 0 ::: pushB256 lockKey ::: Ninst.tstore ::: Func.stop) _
  func_run (6) [0, expirySlot pauser]
  case h_ext =>
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_zero_of_le halign (by omega)
  case h_val =>
    simpa [expirySlot, slot] using
      congrArg (fun x : B256 => (regionWord expiryRegion).or x) hcaller
  case a =>
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    have hg : G + 1512 + storeCost - 16 = G + 1496 + storeCost := by omega
    rw [hg]
    exact hstore

/-! ## The two `pauseSuccess` arms

The count branch is world-dependent, so the two arms are separate lemmas —
both exercised by the two witness worlds: row 19 retires the pauser (count
zero, stored expiry zero) and row 18 retains it (count nonzero, stored expiry
the checked `interval + timestamp`). -/

private theorem temporalSloadCost_congr
    (sevm : Sevm) (base base' : Devm) (k : B256)
    (h : base.accessedStorageKeys = base'.accessedStorageKeys) :
    temporalSloadCost sevm base k = temporalSloadCost sevm base' k := by
  unfold temporalSloadCost
  rw [h]

private theorem temporalSloadBase_accessedStorageKeys_addLog
    (sevm : Sevm) (base : Devm) (l : Log) (k : B256) :
    (temporalSloadBase sevm (base.addLog l) k).accessedStorageKeys =
      (temporalSloadBase sevm base k).accessedStorageKeys := by
  unfold temporalSloadBase
  by_cases h : (sevm.currentTarget, k) ∈ base.accessedStorageKeys
  · rw [if_pos (show (sevm.currentTarget, k) ∈
      (base.addLog l).accessedStorageKeys from h), if_pos h]
    rfl
  · rw [if_neg (show ¬ (sevm.currentTarget, k) ∈
      (base.addLog l).accessedStorageKeys from h), if_neg h]
    rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
/-- The zero-count arm of `pauseSuccess`: the caller's post-callback assignment
count reads zero, so the walk stores expiry `0`.  Charge `3322` plus the count
`SLOAD` and the expiry `SSTORE`, both hypothesis-supplied: `1791` to the count
key, `16` for the count test and the taken branch and the zero push, and the
finish's `1512`. -/
theorem pauseSuccess_zeroCount_ok_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target duration pauser expiryCurrent expiryOriginal : B256)
    (countCost storeCost G : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hduration : Bytes.toB256
      (img.sliceD (durationWord * 32).toNat 32 0) = duration)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (hcaller : sevm.caller.toB256 = pauser)
    (hcount : base.getStorVal sevm.currentTarget (countSlot pauser) = 0)
    (hcountCost : temporalSloadCost sevm base (countSlot pauser) = countCost)
    (hexpiry : base.getStorVal sevm.currentTarget (expirySlot pauser) =
      expiryCurrent)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot pauser) = expiryOriginal)
    (hwarmExpiry : (sevm.currentTarget, expirySlot pauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal expiryCurrent 0 = storeCost)
    (hstipend : gCallStipend < G + 1496 + storeCost)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, G + 3322 + countCost + storeCost⟩) pauseSuccess
      ((((temporalSstorePost sevm
            (temporalSloadBase sevm
              (base.addLog ⟨sevm.currentTarget,
                [pauseTriggeredEvent, target, pauser], duration.toBytes⟩)
              (countSlot pauser))
            (expirySlot pauser) 0).addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser],
            (0 : B256).toBytes⟩).setMach
        ⟨[], (M.write 0 duration.toBytes).write 0 (0 : B256).toBytes,
          G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
  let eventLog : Log := ⟨sevm.currentTarget,
    [pauseTriggeredEvent, target, pauser], duration.toBytes⟩
  let eventBase := base.addLog eventLog
  let countBase := temporalSloadBase sevm eventBase (countSlot pauser)
  have hdurationCovered : (durationWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (durationWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hzeroCovered : 0 + 32 ≤ M.size := by omega
  have hdurationMemory : (M.read (durationWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hdurationCovered)]
  have hdurationValue :
      (M.read (durationWord * 32).toNat 32).1.toB256 = duration := by
    rw [Mem.Reads.read hreads]
    exact hduration
  have hdurBytes : duration.toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes duration
    rw [h] at hlen
    simp at hlen
  have hsizeM' : (M.write 0 duration.toBytes).size = M.size :=
    Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using hzeroCovered)
  have halign' : (M.write 0 duration.toBytes).size % 32 = 0 := by
    rw [hsizeM']; exact halign
  have htargetCovered' :
      (targetWord * 32).toNat + 32 ≤ (M.write 0 duration.toBytes).size := by
    rw [hsizeM']; exact htargetCovered
  have hzeroCovered' : 0 + 32 ≤ (M.write 0 duration.toBytes).size := by
    omega
  have hreads' : Mem.Reads (M.write 0 duration.toBytes)
      (Bytes.writeAt img 0 duration.toBytes) :=
    Mem.Reads.write hwf hreads 0 _
  have htargetValue' :
      ((M.write 0 duration.toBytes).read
        (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact htarget
  have htargetMemory' :
      ((M.write 0 duration.toBytes).read (targetWord * 32).toNat 32).2 =
        M.write 0 duration.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' htargetCovered')]
  have hlogRead' : ((M.write 0 duration.toBytes).read 0 32).1 =
      duration.toBytes := by
    simpa only [B256.length_toBytes] using Mem.read_write_zero M hdurBytes
  have hlogMemory' : ((M.write 0 duration.toBytes).read 0 32).2 =
      M.write 0 duration.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hzeroCovered')]
  -- the finish, entered from the zero push
  have hfinish : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[(0 : B256)], M.write 0 duration.toBytes,
        G + 1512 + storeCost⟩)
      pauseExpiryFinish
      ((((temporalSstorePost sevm countBase (expirySlot pauser) 0).addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser],
            (0 : B256).toBytes⟩).setMach
        ⟨[], (M.write 0 duration.toBytes).write 0 (0 : B256).toBytes,
          G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
    refine pauseExpiryFinish_ok_runCompiled fs sevm countBase
      (M.write 0 duration.toBytes) pauser 0
      expiryCurrent expiryOriginal storeCost G (by omega) halign' hcaller
      ?_ hexpiryOrig ?_ hstoreCost hstipend hstatic
    · rw [show countBase.getStorVal sevm.currentTarget (expirySlot pauser) =
        eventBase.getStorVal sevm.currentTarget (expirySlot pauser) from
          temporalSloadBase_getStorVal sevm eventBase (countSlot pauser) _ _]
      exact hexpiry
    · exact temporalSloadBase_preserves_warm sevm eventBase (countSlot pauser)
        (expirySlot pauser) hwarmExpiry
  -- the count test, the taken branch, and the zero push
  have harm : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[(0 : B256)], M.write 0 duration.toBytes,
        G + 1531 + storeCost⟩)
      (Ninst.iszero :::
        ((pushB256 0 ::: pauseExpiryFinish) <?>
          (checkedHeartbeatExpiry <| pauseExpiryFinish)))
      ((((temporalSstorePost sevm countBase (expirySlot pauser) 0).addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser],
            (0 : B256).toBytes⟩).setMach
        ⟨[], (M.write 0 duration.toBytes).write 0 (0 : B256).toBytes,
          G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
    func_run (3) [1]
    have hg : G + 1531 + storeCost - 19 = G + 1512 + storeCost := by omega
    rw [hg]
    exact hfinish
  -- the count read
  have hsload : Ninst.RunCompiled sevm
      (eventBase.setMach ⟨[countSlot pauser], M.write 0 duration.toBytes,
        G + 1531 + storeCost + countCost⟩)
      Ninst.sload
      (countBase.setMach ⟨[(0 : B256)], M.write 0 duration.toBytes,
        G + 1531 + storeCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm) (base := eventBase)
      (key := countSlot pauser) (value := 0) (stack := [])
      (M := M.write 0 duration.toBytes)
      (G := G + 1531 + storeCost) hcount (by simp)
    rw [show temporalSloadCost sevm eventBase (countSlot pauser) =
      countCost from hcountCost] at h
    exact h
  -- the event prefix
  func_run (14) [3, 0, 3, 1756, countSlot pauser]
  all_goals try simp_rw [hdurationMemory]
  all_goals try simp_rw [hdurationValue]
  all_goals try simp_rw [show ((0 : B256) * 32).toNat = 0 by decide]
  all_goals try simp_rw [htargetMemory']
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hdurationCovered]
    norm_num [gVerylow]
  case h_ext =>
    exact Devm.extCost_zero_of_le halign hzeroCovered
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign' htargetCovered']
    norm_num [gVerylow]
  case h_cost =>
    simp only [show ((1 : B256) * 32).toNat = 32 by decide]
    rw [Devm.extCost_zero_of_le halign' hzeroCovered']
    norm_num [gLog, gLogdata, gLogtopic]
  case h_val =>
    simpa [countSlot, slot] using
      congrArg (fun x : B256 => (regionWord countRegion).or x) hcaller
  case a =>
    simp only [show ((1 : B256) * 32).toNat = 32 by decide]
    rw [htargetValue', hlogRead', hlogMemory', hcaller]
    have hg : G + 3322 + countCost + storeCost - 1791 =
        G + 1531 + storeCost + countCost := by omega
    rw [hg]
    exact Func.RunCompiled.next hsload harm

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
/-- The checked-count arm of `pauseSuccess`: the caller's post-callback
assignment count reads nonzero and the checked heartbeat sum does not wrap, so
the walk stores expiry `interval + timestamp`.  Charge `3351` plus the count
and interval `SLOAD`s and the expiry `SSTORE`, all hypothesis-supplied:
`1791` to the count key, `16` for the count test and its fall-through branch,
`5` to the interval key, `27` for the checked addition and its overflow probe,
and the finish's `1512`. -/
theorem pauseSuccess_checkedCount_ok_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (M : Mem) (img : Bytes)
    (target duration pauser count interval expiryCurrent expiryOriginal : B256)
    (countCost intervalCost storeCost G : Nat)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hduration : Bytes.toB256
      (img.sliceD (durationWord * 32).toNat 32 0) = duration)
    (hsize : 768 ≤ M.size) (halign : M.size % 32 = 0)
    (hcaller : sevm.caller.toB256 = pauser)
    (hcount : base.getStorVal sevm.currentTarget (countSlot pauser) = count)
    (hcountNz : count ≠ 0)
    (hcountCost : temporalSloadCost sevm base (countSlot pauser) = countCost)
    (hinterval : base.getStorVal sevm.currentTarget heartbeatIntervalSlot =
      interval)
    (hintervalCost : temporalSloadCost sevm
      (temporalSloadBase sevm base (countSlot pauser))
      heartbeatIntervalSlot = intervalCost)
    (hnof : B256.Nof sevm.benvStat.time interval)
    (hexpiry : base.getStorVal sevm.currentTarget (expirySlot pauser) =
      expiryCurrent)
    (hexpiryOrig : getOrigStorVal sevm sevm.currentTarget
      (expirySlot pauser) = expiryOriginal)
    (hwarmExpiry : (sevm.currentTarget, expirySlot pauser) ∈
      base.accessedStorageKeys)
    (hstoreCost : sstoreValueCost expiryOriginal expiryCurrent
      (interval + sevm.benvStat.time) = storeCost)
    (hstipend : gCallStipend < G + 1496 + storeCost)
    (hstatic : sevm.isStatic = false) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M,
        G + 3351 + countCost + intervalCost + storeCost⟩) pauseSuccess
      ((((temporalSstorePost sevm
            (temporalSloadBase sevm
              (temporalSloadBase sevm
                (base.addLog ⟨sevm.currentTarget,
                  [pauseTriggeredEvent, target, pauser], duration.toBytes⟩)
                (countSlot pauser))
              heartbeatIntervalSlot)
            (expirySlot pauser) (interval + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser],
            (interval + sevm.benvStat.time).toBytes⟩).setMach
        ⟨[], (M.write 0 duration.toBytes).write 0
          (interval + sevm.benvStat.time).toBytes, G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
  let eventLog : Log := ⟨sevm.currentTarget,
    [pauseTriggeredEvent, target, pauser], duration.toBytes⟩
  let eventBase := base.addLog eventLog
  let countBase := temporalSloadBase sevm eventBase (countSlot pauser)
  let intervalBase := temporalSloadBase sevm countBase heartbeatIntervalSlot
  have hdurationCovered : (durationWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (durationWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have htargetCovered : (targetWord * 32).toNat + 32 ≤ M.size := by
    have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
    omega
  have hzeroCovered : 0 + 32 ≤ M.size := by omega
  have hdurationMemory : (M.read (durationWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign hdurationCovered)]
  have hdurationValue :
      (M.read (durationWord * 32).toNat 32).1.toB256 = duration := by
    rw [Mem.Reads.read hreads]
    exact hduration
  have hdurBytes : duration.toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes duration
    rw [h] at hlen
    simp at hlen
  have hsizeM' : (M.write 0 duration.toBytes).size = M.size :=
    Mem.size_write_of_le (by
      simpa only [B256.length_toBytes] using hzeroCovered)
  have halign' : (M.write 0 duration.toBytes).size % 32 = 0 := by
    rw [hsizeM']; exact halign
  have htargetCovered' :
      (targetWord * 32).toNat + 32 ≤ (M.write 0 duration.toBytes).size := by
    rw [hsizeM']; exact htargetCovered
  have hzeroCovered' : 0 + 32 ≤ (M.write 0 duration.toBytes).size := by
    omega
  have hreads' : Mem.Reads (M.write 0 duration.toBytes)
      (Bytes.writeAt img 0 duration.toBytes) :=
    Mem.Reads.write hwf hreads 0 _
  have htargetValue' :
      ((M.write 0 duration.toBytes).read
        (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads']
    rw [Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      rw [B256.length_toBytes]; decide)]
    exact htarget
  have htargetMemory' :
      ((M.write 0 duration.toBytes).read (targetWord * 32).toNat 32).2 =
        M.write 0 duration.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' htargetCovered')]
  have hlogRead' : ((M.write 0 duration.toBytes).read 0 32).1 =
      duration.toBytes := by
    simpa only [B256.length_toBytes] using Mem.read_write_zero M hdurBytes
  have hlogMemory' : ((M.write 0 duration.toBytes).read 0 32).2 =
      M.write 0 duration.toBytes := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign' hzeroCovered')]
  -- the finish, entered with the checked sum
  have hfinish : Func.RunCompiled fs sevm
      (intervalBase.setMach ⟨[interval + sevm.benvStat.time],
        M.write 0 duration.toBytes, G + 1512 + storeCost⟩)
      pauseExpiryFinish
      ((((temporalSstorePost sevm intervalBase (expirySlot pauser)
            (interval + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser],
            (interval + sevm.benvStat.time).toBytes⟩).setMach
        ⟨[], (M.write 0 duration.toBytes).write 0
          (interval + sevm.benvStat.time).toBytes, G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
    refine pauseExpiryFinish_ok_runCompiled fs sevm intervalBase
      (M.write 0 duration.toBytes) pauser (interval + sevm.benvStat.time)
      expiryCurrent expiryOriginal storeCost G (by omega) halign' hcaller
      ?_ hexpiryOrig ?_ hstoreCost hstipend hstatic
    · rw [show intervalBase.getStorVal sevm.currentTarget
          (expirySlot pauser) =
        countBase.getStorVal sevm.currentTarget (expirySlot pauser) from
          temporalSloadBase_getStorVal sevm countBase heartbeatIntervalSlot
            _ _,
        show countBase.getStorVal sevm.currentTarget (expirySlot pauser) =
          eventBase.getStorVal sevm.currentTarget (expirySlot pauser) from
            temporalSloadBase_getStorVal sevm eventBase (countSlot pauser)
              _ _]
      exact hexpiry
    · exact temporalSloadBase_preserves_warm sevm countBase
        heartbeatIntervalSlot (expirySlot pauser)
        (temporalSloadBase_preserves_warm sevm eventBase (countSlot pauser)
          (expirySlot pauser) hwarmExpiry)
  -- the checked addition and its overflow probe
  have hsum : Func.RunCompiled fs sevm
      (intervalBase.setMach ⟨[interval, sevm.benvStat.time],
        M.write 0 duration.toBytes, G + 1539 + storeCost⟩)
      (Ninst.add ::: Ninst.dup 0 ::: Ninst.timestamp ::: Ninst.swap 0 :::
        Ninst.lt :::
        ((Func.call arithmeticPanicSlot) <?> pauseExpiryFinish))
      ((((temporalSstorePost sevm intervalBase (expirySlot pauser)
            (interval + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser],
            (interval + sevm.benvStat.time).toBytes⟩).setMach
        ⟨[], (M.write 0 duration.toBytes).write 0
          (interval + sevm.benvStat.time).toBytes, G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
    func_run (6) [interval + sevm.benvStat.time, 0]
    · exact ltCheck_checkedSum_eq_zero hnof
    · have hg : G + 1539 + storeCost - 27 = G + 1512 + storeCost := by omega
      rw [hg]
      exact hfinish
  -- the interval read
  have hintervalSload : Ninst.RunCompiled sevm
      (countBase.setMach ⟨[heartbeatIntervalSlot, sevm.benvStat.time],
        M.write 0 duration.toBytes,
        G + 1539 + storeCost + intervalCost⟩)
      Ninst.sload
      (intervalBase.setMach ⟨[interval, sevm.benvStat.time],
        M.write 0 duration.toBytes, G + 1539 + storeCost⟩) := by
    have hvalue : countBase.getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval := by
      rw [show countBase.getStorVal sevm.currentTarget
          heartbeatIntervalSlot =
        eventBase.getStorVal sevm.currentTarget heartbeatIntervalSlot from
          temporalSloadBase_getStorVal sevm eventBase (countSlot pauser) _ _]
      exact hinterval
    have hcost : temporalSloadCost sevm countBase heartbeatIntervalSlot =
        intervalCost :=
      (temporalSloadCost_congr sevm countBase
        (temporalSloadBase sevm base (countSlot pauser))
        heartbeatIntervalSlot
        (temporalSloadBase_accessedStorageKeys_addLog sevm base eventLog
          (countSlot pauser))).trans hintervalCost
    have h := temporal_sload_runCompiled (sevm := sevm) (base := countBase)
      (key := heartbeatIntervalSlot) (value := interval)
      (stack := [sevm.benvStat.time]) (M := M.write 0 duration.toBytes)
      (G := G + 1539 + storeCost) hvalue (by simp)
    rw [hcost] at h
    exact h
  -- the count test, the fall-through branch, and the checked-arm prefix
  have harm : Func.RunCompiled fs sevm
      (countBase.setMach ⟨[count], M.write 0 duration.toBytes,
        G + 1560 + intervalCost + storeCost⟩)
      (Ninst.iszero :::
        ((pushB256 0 ::: pauseExpiryFinish) <?>
          (checkedHeartbeatExpiry <| pauseExpiryFinish)))
      ((((temporalSstorePost sevm intervalBase (expirySlot pauser)
            (interval + sevm.benvStat.time)).addLog
          ⟨sevm.currentTarget, [heartbeatUpdatedEvent, pauser],
            (interval + sevm.benvStat.time).toBytes⟩).setMach
        ⟨[], (M.write 0 duration.toBytes).write 0
          (interval + sevm.benvStat.time).toBytes, G⟩).setTransVal
        sevm.currentTarget lockKey 0) := by
    func_run (4) [0]
    · rw [B256.eqCheck, if_neg hcountNz]
    · have hg : G + 1560 + intervalCost + storeCost - 21 =
          G + 1539 + storeCost + intervalCost := by omega
      rw [hg]
      exact Func.RunCompiled.next hintervalSload hsum
  -- the count read
  have hsload : Ninst.RunCompiled sevm
      (eventBase.setMach ⟨[countSlot pauser], M.write 0 duration.toBytes,
        G + 1560 + intervalCost + storeCost + countCost⟩)
      Ninst.sload
      (countBase.setMach ⟨[count], M.write 0 duration.toBytes,
        G + 1560 + intervalCost + storeCost⟩) := by
    have h := temporal_sload_runCompiled (sevm := sevm) (base := eventBase)
      (key := countSlot pauser) (value := count) (stack := [])
      (M := M.write 0 duration.toBytes)
      (G := G + 1560 + intervalCost + storeCost) hcount (by simp)
    rw [show temporalSloadCost sevm eventBase (countSlot pauser) =
      countCost from hcountCost] at h
    exact h
  -- the event prefix
  func_run (14) [3, 0, 3, 1756, countSlot pauser]
  all_goals try simp_rw [hdurationMemory]
  all_goals try simp_rw [hdurationValue]
  all_goals try simp_rw [show ((0 : B256) * 32).toNat = 0 by decide]
  all_goals try simp_rw [htargetMemory']
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign hdurationCovered]
    norm_num [gVerylow]
  case h_ext =>
    exact Devm.extCost_zero_of_le halign hzeroCovered
  case h_cost =>
    rw [Devm.extCost_zero_of_le halign' htargetCovered']
    norm_num [gVerylow]
  case h_cost =>
    simp only [show ((1 : B256) * 32).toNat = 32 by decide]
    rw [Devm.extCost_zero_of_le halign' hzeroCovered']
    norm_num [gLog, gLogdata, gLogtopic]
  case h_val =>
    simpa [countSlot, slot] using
      congrArg (fun x : B256 => (regionWord countRegion).or x) hcaller
  case a =>
    simp only [show ((1 : B256) * 32).toNat = 32 by decide]
    rw [htargetValue', hlogRead', hlogMemory', hcaller]
    have hg : G + 3351 + countCost + intervalCost + storeCost - 1791 =
        G + 1560 + intervalCost + storeCost + countCost := by omega
    rw [hg]
    exact Func.RunCompiled.next hsload harm

/-! ## The `pauseAfterSet` leg -/

/-- The staged image after `pauseAfterSet`'s three selector/argument writes:
the `pauseFor` selector word at `256`, the duration argument at `288`, then
the `isPaused` selector word overwriting `256`. -/
def pauseStagedMemory (M : Mem) (duration : B256) : Mem :=
  ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes).write
    256 isPausedSelector.toBytes

/-- The memory `decodePausedResult` leaves at the `pauseSuccess` boundary: the
staged image with the `isPaused()` returndata word `1` retained at offset
zero. -/
def pauseDecodedMemory (M : Mem) (duration : B256) : Mem :=
  (pauseStagedMemory M duration).write 0 (1 : B256).toBytes

set_option maxRecDepth 32768 in
set_option maxHeartbeats 3200000 in
/-- `pauseAfterSet` from its entry to the `pauseSuccess` boundary, `.ok`
flavour: through the target-code guard (charge hypothesis-supplied, warmth
being a frame fact), the `pauseFor(uint256)` `CALL` and the `isPaused()`
`STATICCALL` — both crossing the responder callee, each costing exactly
`117 = gasWarmAccess + 17` — and the decode.  The continuation is entered at
the exact boundary state, which exists only behind the crossings'
existentials, so it is universally quantified and pinned by projection facts:
machine fields, result fields, meta-set memberships, and the state as the
double zero-value `subBal`/`addBal` chain.

Charge `427 + codeCost`: `27 + codeCost` for the guard, `41` for the `CALL`
staging, `117` for the `CALL`, `44` to the `STATICCALL`, `117` for it, and
`81` for the decode into `pauseSuccess`. -/
theorem pauseAfterSet_toSuccess_runCompiled
    (fs : List Func) (sevm : Sevm) (base : Devm)
    (target duration : B256) (M : Mem) (img : Bytes)
    (codeCost Gb : Nat) (post : Devm)
    (hwf : Mem.Wf M)
    (hreads : Mem.Reads M img)
    (htarget : Bytes.toB256
      (img.sliceD (targetWord * 32).toNat 32 0) = target)
    (hduration : Bytes.toB256
      (img.sliceD (durationWord * 32).toNat 32 0) = duration)
    (hsize : M.size = 768)
    (hcodeCost : temporalAccountAccessCost base target.toAdr = codeCost)
    (hcalleeCode : base.getCode target.toAdr = calleeCode)
    (hdepth : sevm.depth ≠ 0)
    (hnp : sevm.benvStat.rules.isPrecomp target.toAdr = false)
    (hbound : Gb + 359 < 2 ^ 256)
    (hsuccess : ∀ mid : Devm,
      mid.stack = [] →
      mid.memory = pauseDecodedMemory M duration →
      mid.gasLeft = Gb →
      mid.error = base.error →
      mid.output = base.output →
      mid.returnData = (1 : B256).toBytes →
      mid.logs = base.logs →
      mid.refundCounter = base.refundCounter →
      mid.accountsToDelete.isEmpty = base.accountsToDelete.isEmpty →
      mid.transientStorage = base.transientStorage →
      (∀ k, k ∈ mid.accessedStorageKeys ↔ k ∈ base.accessedStorageKeys) →
      (∀ a, a ∈ mid.accessedAddresses ↔
        (a = target.toAdr ∨ a ∈ base.accessedAddresses)) →
      (∃ st₁ st₂ : State,
        base.state.subBal sevm.currentTarget 0 = some st₁ ∧
        (st₁.addBal target.toAdr 0).subBal sevm.currentTarget 0 = some st₂ ∧
        mid.state = st₂.addBal target.toAdr 0) →
      Func.RunCompiled fs sevm mid pauseSuccess post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], M, Gb + 427 + codeCost⟩) pauseAfterSet post := by
  have halign : M.size % 32 = 0 := by omega
  -- the staged images and their windows
  have hwf1 : Mem.Wf (M.write 256 pauseForSelector.toBytes) := hwf.write _ _
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
  -- entry-image reads
  have htargetMemory0 : (M.read (targetWord * 32).toNat 32).2 = M := by
    rw [Mem.read_snd_eq_self (memExtSize_of_le halign (by
      have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
      omega))]
  have htargetValue0 :
      (M.read (targetWord * 32).toNat 32).1.toB256 = target := by
    rw [Mem.Reads.read hreads]
    exact htarget
  -- duration read from the selector-staged image
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
  -- target read from the two-word-staged image
  have hreads2 : Mem.Reads
      ((M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes)
      (Bytes.writeAt (Bytes.writeAt img 256 pauseForSelector.toBytes) 288
        duration.toBytes) :=
    Mem.Reads.write hwf1 hreads1 288 _
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
  -- target read from the fully staged image
  have hreads3 : Mem.Reads (((M.write 256 pauseForSelector.toBytes).write 288
      duration.toBytes).write 256 isPausedSelector.toBytes)
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 256
        pauseForSelector.toBytes) 288 duration.toBytes) 256
        isPausedSelector.toBytes) :=
    Mem.Reads.write hwf2 hreads2 256 _
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
  -- the decoded word read back
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
  -- the first crossing
  obtain ⟨post1, hrun1, hstk1, hmem1, hgas1, herr1, hout1, hret1, hlogs1,
    hrefund1, hatd1, htrans1, hask1, haa1, st₁, hsub1, hstate1⟩ :=
    responder_call_crossing (sevm := sevm)
      (devm := (temporalAccountAccessBase base target.toAdr).setMach
        ⟨[Nat.toB256 (Gb + 359), target, 0, 284, 36, 0, 0],
          (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
          Gb + 359⟩)
      (target := target) (iiw := 284) (isw := 36) (oiw := 0) (osw := 0)
      (s := []) (G := Gb + 359)
      rfl rfl
      (by
        show ((temporalAccountAccessBase base target.toAdr).setMach
          ⟨[Nat.toB256 (Gb + 359), target, 0, 284, 36, 0, 0],
            (M.write 256 pauseForSelector.toBytes).write 288
              duration.toBytes, Gb + 359⟩).extCost _ = 0
        exact Devm.extCost_covered (by rw [hsize2]; decide))
      (by
        show (temporalAccountAccessBase base target.toAdr).getCode
          target.toAdr = calleeCode
        rw [temporalAccountAccessBase_getCode]
        exact hcalleeCode)
      (temporalAccountAccessBase_warm base target.toAdr)
      hdepth hnp (by omega) hbound (by simp)
  have hgas1' : post1.gasLeft = Gb + 242 := by
    rw [hgas1]
    omega
  have hmem1' : post1.memory =
      (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes := by
    simp only [Devm.memory_setMach] at hmem1
    rw [hmem1,
      show (1 : B256).toBytes.take ((0 : B256)).toNat = [] by decide,
      show ((0 : B256)).toNat = 0 by decide,
      Mem.extends_covered (by rw [hsize2]; decide)]
    rfl
  have heta1 : post1 = post1.setMach ⟨[1],
      (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
      Gb + 242⟩ := by
    rw [← hstk1, ← hmem1', ← hgas1']
    rfl
  -- the second crossing
  have hcode1 : post1.state.getCode target.toAdr = calleeCode := by
    rw [hstate1, State.addBal_getCode, State.subBal_getCode hsub1]
    show (temporalAccountAccessBase base target.toAdr).state.getCode
      target.toAdr = calleeCode
    rw [temporalAccountAccessBase_state]
    exact hcalleeCode
  obtain ⟨post2, hrun2, hstk2, hmem2, hgas2, herr2, hout2, hret2, hlogs2,
    hrefund2, hatd2, htrans2, hask2, haa2, st₂, hsub2, hstate2⟩ :=
    responder_statcall_crossing (sevm := sevm)
      (devm := post1.setMach
        ⟨[Nat.toB256 (Gb + 198), target, 284, 4, 0, 32],
          ((M.write 256 pauseForSelector.toBytes).write 288
            duration.toBytes).write 256 isPausedSelector.toBytes,
          Gb + 198⟩)
      (target := target) (iiw := 284) (isw := 4) (oiw := 0) (osw := 32)
      (s := []) (G := Gb + 198)
      rfl rfl
      (by
        show (post1.setMach
          ⟨[Nat.toB256 (Gb + 198), target, 284, 4, 0, 32],
            ((M.write 256 pauseForSelector.toBytes).write 288
              duration.toBytes).write 256 isPausedSelector.toBytes,
            Gb + 198⟩).extCost _ = 0
        exact Devm.extCost_covered (by rw [hsize3]; decide))
      (by
        show post1.state.getCode target.toAdr = calleeCode
        exact hcode1)
      ((haa1 target.toAdr).mpr (temporalAccountAccessBase_warm base
        target.toAdr))
      hdepth hnp (by omega) (by omega) (by simp)
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
  -- the boundary state's facts, chained through both crossings
  have hltFlag : (Nat.toB256 post2.returnData.length <? (32 : B256)) = 0 := by
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
      k ∈ base.accessedStorageKeys := by
    intro k
    refine (hask2 k).trans ((hask1 k).trans ?_)
    show k ∈ (temporalAccountAccessBase base target.toAdr
      ).accessedStorageKeys ↔ k ∈ base.accessedStorageKeys
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
  have hsub2' : (st₁.addBal target.toAdr 0).subBal sevm.currentTarget 0 =
      some st₂ := by
    rw [← hstate1]
    exact hsub2
  -- segment C: the decode, from the second crossing to the boundary
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
      rw [hg]
      refine hsuccess _ rfl ?_ rfl herrB houtB hret2 hlogsB hrefundB hatdB
        htransB haskB haaB ⟨st₁, st₂, hsub1', hsub2', hstate2⟩
      show ((pauseDecodedMemory M duration).read 0 32).2 =
        pauseDecodedMemory M duration
      exact hdecodedMemory
  -- segment B: from the first crossing to the second
  have hB : Func.RunCompiled fs sevm
      (post1.setMach ⟨[1],
        (M.write 256 pauseForSelector.toBytes).write 288 duration.toBytes,
        Gb + 242⟩)
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?>
          (pushB256 isPausedSelector ::: mstoreAt 8 +++
            pushList [32, 0, 4, 0x11c] +++ loadWord targetWord +++
            Ninst.gas ::: Ninst.statcall ::: Ninst.iszero :::
            ((Func.call bubbleRevertSlot) <?> decodePausedResult)))) post := by
    func_run (12) [0, 0, 3]
    all_goals try simp_rw [show ((8 : B256) * 32).toNat = 256 by decide]
    all_goals try simp_rw [htargetMemory3]
    case h_ext =>
      exact Devm.extCost_zero_of_le halign2 (by omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign3 (by
        have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
        omega)]
      norm_num [gVerylow]
    case a =>
      rw [htargetValue3]
      have hg : Gb + 242 - 44 = Gb + 198 := by omega
      rw [hg]
      refine Func.RunCompiled.next hrun2 ?_
      rw [heta2]
      exact hC
  -- segment A2: the guard's live arm and the CALL staging
  have hA2 : Func.RunCompiled fs sevm
      ((temporalAccountAccessBase base target.toAdr).setMach
        ⟨[calleeCode.size.toB256, target], M, Gb + 418⟩)
      (Ninst.iszero :::
        ((Func.call emptyRevertSlot) <?>
          (Ninst.pop :::
            pushB256 pauseForSelector ::: mstoreAt 8 +++
            loadWord durationWord +++ mstoreAt 9 +++
            pushList [0, 0, 36, 0x11c, 0] +++ loadWord targetWord +++
            Ninst.gas ::: Ninst.call ::: Ninst.iszero :::
            ((Func.call bubbleRevertSlot) <?>
              (pushB256 isPausedSelector ::: mstoreAt 8 +++
                pushList [32, 0, 4, 0x11c] +++ loadWord targetWord +++
                Ninst.gas ::: Ninst.statcall ::: Ninst.iszero :::
                ((Func.call bubbleRevertSlot) <?> decodePausedResult))))))
      post := by
    func_run (18) [0, 0, 3, 0, 3]
    all_goals try simp_rw [show ((8 : B256) * 32).toNat = 256 by decide]
    all_goals try simp_rw [show ((9 : B256) * 32).toNat = 288 by decide]
    all_goals try simp_rw [hdurationMemory1]
    all_goals try simp_rw [hdurationValue1]
    all_goals try simp_rw [htargetMemory2]
    case h_ext =>
      exact Devm.extCost_zero_of_le halign (by omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le (by omega) (by
        have hoff : (durationWord * 32).toNat + 32 ≤ 768 := by decide
        omega)]
      norm_num [gVerylow]
    case h_ext =>
      exact Devm.extCost_zero_of_le (by omega) (by omega)
    case h_cost =>
      rw [Devm.extCost_zero_of_le halign2 (by
        have hoff : (targetWord * 32).toNat + 32 ≤ 768 := by decide
        omega)]
      norm_num [gVerylow]
    case a =>
      rw [htargetValue2]
      have hg : Gb + 418 - 59 = Gb + 359 := by omega
      rw [hg]
      refine Func.RunCompiled.next hrun1 ?_
      rw [heta1]
      exact hB
  -- the entry: the target load and the code-size guard
  have hextStep : Ninst.RunCompiled sevm
      (base.setMach ⟨[target, target], M, Gb + 418 + codeCost⟩)
      Ninst.extcodesize
      ((temporalAccountAccessBase base target.toAdr).setMach
        ⟨[calleeCode.size.toB256, target], M, Gb + 418⟩) := by
    have h := temporal_extcodesize_runCompiled (sevm := sevm) (base := base)
      (x := target) (v := calleeCode.size.toB256) (stack := [target])
      (M := M) (G := Gb + 418)
      (by rw [hcalleeCode]) (by simp)
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
    have hg : Gb + 427 + codeCost - 9 = Gb + 418 + codeCost := by omega
    rw [hg]
    exact Func.RunCompiled.next hextStep hA2

end Blanc.LidoCircuitBreaker
