import Blanc.ForwardCall
import Blanc.LidoCircuitBreakerPauseAttainment

/-!
The pause walk's **witness worlds** and **responder crossings**.

`Blanc/LidoCircuitBreakerPauseWalk.lean` carries the `.ok`-flavour walk legs of
a successful `pause(address)` up to the boundaries the register side owns.
What that walk cannot supply by itself is the far side of `pauseAfterSet`'s two
external calls: a callee that actually answers the `pauseFor(uint256)` `CALL`
and the `isPaused()` `STATICCALL` with a clean word `1`.  This leaf supplies
that callee and the two compiled-instruction crossings through it, plus the two
concrete entry worlds at which the walk's remaining premises — Registry shape,
heartbeat liveness, configured duration, account codes — all hold at once.

Three layers, none of which composes the walk itself:

* **The responder callee** (`calleeMain` … `callee_exec`): a selector-blind
  program that returns the 32-byte canonical word `1` on every entry.  It
  serves both external calls at once — the parent reads only the success flag
  after `pauseFor` and the returndata word after `isPaused` — and performs no
  state-changing operation, so the static flag of the second call costs it
  nothing.
* **The crossings** (`runCompiled_call_zero_value_responder`,
  `runCompiled_staticcall_responder`): `Ninst.runCompiled_call_zero_value_codeFree`'s
  skeleton with the code-free child replaced by the responder.  Each exports
  the full post-`CALL` projection list a continuation walk consumes — stack,
  memory, gas, error, output, returndata, logs, refund counter,
  accounts-to-delete, transient storage, both accessed sets, and the state as
  the zero-value `subBal`/`addBal` chain.
* **The worlds** (`pauseWorld…`): the row-19 world (`…Last…`, the pauser's
  single assignment, so the pause retires it and clears its expiry) and the
  row-18 world (`…Retained…`, a second target `t2` keeps the pauser's count
  positive, so the pause writes a fresh checked expiry).  Both are
  Registry-well-formed and witnessed as such.

The walk composition (`pauseWorld_effects`) is deliberately absent: it is owned
by the pause-walk side.  This module stops at world facts and crossing facts.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## The minimal responder callee

Selector-blind: returns the 32-byte canonical word `1` on every entry.  Serves
`pauseFor(uint256)` (parent reads only the flag) and `isPaused()` (returndata
word `1`) at once; no storage writes, no calls, static-safe. -/

def calleeMain : Func :=
  pushB256 1 ::: mstoreAt 0 +++ pushB256 32 ::: pushB256 0 ::: Func.last .return_

def calleeProg : Prog := ⟨calleeMain, []⟩

def calleeBytes : Bytes := (Prog.compile calleeProg).getD []

def calleeCode : ByteArray := ByteArray.mk calleeBytes.toArray

theorem calleeProg_compiles : calleeProg.compiles = true := by
  decide

theorem calleeProg_compile :
    Prog.compile calleeProg = some calleeBytes :=
  Prog.compile_eq_some_getD_of_compiles _ calleeProg_compiles

/-! ## The callee's execution, evaluated through its own walk -/

/-- The callee body from any base state: exact charge `18`, output the 32-byte
canonical word `1`, world untouched, no error introduced, and every
child-incorporated meta field — logs, refund counter, accounts to delete, both
accessed sets — exactly the base's own. -/
theorem calleeMain_runCompiledTo (fs : List Func) (sevm : Sevm) (base : Devm)
    (G : Nat) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 16⟩) calleeMain (.ok post) ∧
      post.error = base.error ∧
      post.output = (1 : B256).toBytes ∧
      post.gasLeft = G ∧
      post.world = base.world ∧
      post.logs = base.logs ∧
      post.refundCounter = base.refundCounter ∧
      post.accountsToDelete = base.accountsToDelete ∧
      post.accessedAddresses = base.accessedAddresses ∧
      post.accessedStorageKeys = base.accessedStorageKeys := by
  apply Exists.intro
  refine ⟨?walk, ?herr, ?hout, ?hgas, ?hworld, ?hlogs, ?hrefund, ?hatd,
    ?haa, ?hask⟩
  case walk =>
    unfold calleeMain mstoreAt
    func_run [3]
    case h_ext =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide]
      exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_return_word (i := 0) (sz := 32) (s := [])
        (e := 0) (G := G) (out := (1 : B256).toBytes)
      · rfl
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide,
          show ((0 : B256) * 32).toNat = 0 by decide]
        exact Devm.extCost_word_word Mem.size_write_word
      · show G + 16 - 16 = G + 0
        omega
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide]
        exact Devm.memRead_word_fst
          (by rw [show ((0 : B256) * 32).toNat = 0 by decide]; rfl)
  all_goals rfl

/-- The callee's total execution: any message installing its code and carrying
gas `G + 17` executes to `.ok` with output the canonical word `1`, leaving the
world untouched and the child-incorporated meta fields at their message-entry
values.  This is the fact the parent's CALL/STATICCALL crossings consume at
`exec cevm`. -/
theorem callee_exec (m : Msg) (G : Nat)
    (hcode : m.code = calleeCode)
    (hgas : m.gas = G + 17) :
    ∃ post,
      exec (initEvm m) = .ok post ∧
      post.error = none ∧
      post.output = (1 : B256).toBytes ∧
      post.gasLeft = G ∧
      post.world = (initDevm m).world ∧
      post.logs = [] ∧
      post.refundCounter = 0 ∧
      post.accountsToDelete = Std.HashSet.emptyWithCapacity ∧
      post.accessedAddresses = m.accessedAddresses ∧
      post.accessedStorageKeys = m.accessedStorageKeys := by
  obtain ⟨post, walk, herr, hout, hgasPost, hworld, hlogs, hrefund, hatd,
    haa, hask⟩ :=
    calleeMain_runCompiledTo [calleeMain] (initSevm m) (initDevm m) G
  refine ⟨post, ?_, herr, hout, hgasPost, hworld, by rw [hlogs]; rfl,
    by rw [hrefund]; rfl, by rw [hatd]; rfl, by rw [haa]; rfl,
    by rw [hask]; rfl⟩
  have hrun : Prog.RunCompiledTo (initSevm m) (initDevm m) calleeProg
      (.ok post) := by
    refine Prog.runCompiledTo_intro (G := G + 16)
      (mid := (initDevm m).setMach ⟨[], Mem.empty, G + 16⟩) ?_ rfl walk
    show m.gas = G + 16 + gJumpdest
    simp only [gJumpdest]
    omega
  have hcompile : some (initSevm m).code.toList = Prog.compile calleeProg := by
    show some m.code.toList = _
    rw [hcode, calleeProg_compile]
    simp [calleeCode, ByteArray.toList_eq_toList_data]
  exact Prog.exec_of_runCompiledTo hrun hcompile

/-! ## The two responder crossings

`Ninst.runCompiled_call_zero_value_codeFree`'s skeleton with the code-free
child replaced by the responder: the child fact is `callee_exec`, and the
settle step carries the child's `error = none` instead of `rfl`.  Each crossing
exports the full projection list a continuation walk consumes; the accessed
sets are exported as membership equivalences because
`incorporateChildOnSuccess` unions the parent's set with the child's copy of
that same set, and `Std.HashSet` union is extensional in membership only. -/

/-- The delegation resolution leaves the transient store and the accessed
storage keys alone; only the accessed-address set can move. -/
private lemma accessDelegation_worldMeta {devm d1 : Devm} {a dadr : Adr}
    {dp : Bool} {code : ByteArray} {dgc : Nat}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    d1.transientStorage = devm.transientStorage ∧
      d1.accessedStorageKeys = devm.accessedStorageKeys := by
  unfold accessDelegation at h
  rcases hd : getDelegatedCodeAddress (devm.state.getCode a) with _ | adr <;>
    simp only [hd] at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h
    exact ⟨rfl, rfl⟩

/-- The `value = 0` `CALL` crossing with the responder callee entered.  The
child spends exactly `17` of its `mcs` and answers the canonical word `1`, so
the parent resumes with flag `1`, the child's word as returndata, its own
output window written with that word's `osw`-truncation, and every other
projection its trunk established. -/
lemma runCompiled_call_zero_value_responder {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
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
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_code : code = calleeCode)
    (h_mcs : 17 ≤ mcs)
    (h_room : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .call) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) + (mcs - 17) ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ d1.accessedAddresses) ∧
      ∃ stmid,
        devm.state.subBal sevm.currentTarget 0 = some stmid ∧
        post.state = stmid.addBal cw.toAdr 0 := by
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
  obtain ⟨out, hexec, herr, hout, hgasOut, hworld, hlogsOut, hrefundOut,
    hatdOut, haaOut, haskOut⟩ :=
    callee_exec (msg.withBenv benv') (mcs - 17)
      (by change code = calleeCode; exact h_code)
      (by change mcs = mcs - 17 + 17; omega)
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
  have hd1refund : d1.refundCounter = devm.refundCounter := hd1frame.2.2.1
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
  have hrun : Ninst.RunCompiled sevm devm (.exec .call) post :=
    Ninst.runCompiled_call_zero_value h_stk h_ext h_del h_acc h_split h_gas
      h_depth (by simpa [p, msg]) (by simpa [p, msg] using hres)
  have hpask : p.accessedStorageKeys = devm.accessedStorageKeys := hd1wm.2
  have haskOut' : out.accessedStorageKeys = devm.accessedStorageKeys :=
    haskOut.trans hd1wm.2
  have hpaa : p.accessedAddresses = d1.accessedAddresses := rfl
  have haaOut' : out.accessedAddresses = d1.accessedAddresses := haaOut
  refine ⟨post, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    stmid, ?_, ?_⟩
  · show ((((incorporateChildOnSuccess p out out.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + out.gasLeft⟩).memWrite
        oiw.toNat (out.output.take osw.toNat))).stack = 1 :: s
    rw [Devm.memWrite_stack, Devm.stack_setMach]
    change 1 :: d1.stack = 1 :: s
    rw [hd1stack]
  · show ((((incorporateChildOnSuccess p out out.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + out.gasLeft⟩).memWrite
        oiw.toNat (out.output.take osw.toNat))).memory = _
    rw [Devm.memWrite_memory, Devm.memory_setMach, hout]
    change (d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
        oiw.toNat ((1 : B256).toBytes.take osw.toNat) = _
    rw [hd1mem]
  · show ((((incorporateChildOnSuccess p out out.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + out.gasLeft⟩).memWrite
        oiw.toNat (out.output.take osw.toNat))).gasLeft = _
    rw [Devm.memWrite_gasLeft, Devm.gasLeft_setMach, hgasOut]
    change d1.gasLeft - (mcc + ext) + (mcs - 17) = _
    rfl
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
    rw [show out.transientStorage =
      (initDevm (msg.withBenv benv')).transientStorage from
        congrArg World.transientStorage hworld]
    exact hd1wm.1
  · intro k
    change k ∈ p.accessedStorageKeys.union out.accessedStorageKeys ↔
      k ∈ devm.accessedStorageKeys
    rw [hpask, haskOut']
    exact ⟨fun h => (Std.HashSet.mem_union_iff.mp h).elim id id,
      fun h => Std.HashSet.mem_union_iff.mpr (Or.inl h)⟩
  · intro a
    change a ∈ p.accessedAddresses.union out.accessedAddresses ↔
      a ∈ d1.accessedAddresses
    rw [hpaa, haaOut']
    exact ⟨fun h => (Std.HashSet.mem_union_iff.mp h).elim id id,
      fun h => Std.HashSet.mem_union_iff.mpr (Or.inl h)⟩
  · rw [← hd1state]
    have hsub' : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, callSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsub'
    exact hsub'
  · change out.state = stmid.addBal cw.toAdr 0
    rw [show out.state = (initDevm (msg.withBenv benv')).state from
      congrArg World.state hworld]
    rfl

/-- The `STATICCALL` sibling.  Same six stack operands as the value-zero part
of `CALL` minus the value word, same `callSpawnParent`, same `.call` resume
tag, and the same responder child — entered static, which costs it nothing
because `calleeMain` performs no state-changing operation. -/
lemma runCompiled_staticcall_responder {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
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
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : mcc + ext ≤ d1.gasLeft)
    (h_depth : sevm.depth ≠ 0)
    (h_nonprecompile : sevm.benvStat.rules.isPrecomp dadr = false)
    (h_code : code = calleeCode)
    (h_mcs : 17 ≤ mcs)
    (h_room : s.length < 1024) :
    ∃ post,
      Ninst.RunCompiled sevm devm (.exec .staticcall) post ∧
      post.stack = 1 :: s ∧
      post.memory = (devm.memory.extends
        [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
          oiw.toNat ((1 : B256).toBytes.take osw.toNat) ∧
      post.gasLeft = d1.gasLeft - (mcc + ext) + (mcs - 17) ∧
      post.error = devm.error ∧ post.output = devm.output ∧
      post.returnData = (1 : B256).toBytes ∧
      post.logs = devm.logs ∧
      post.refundCounter = devm.refundCounter ∧
      post.accountsToDelete.isEmpty = devm.accountsToDelete.isEmpty ∧
      post.transientStorage = devm.transientStorage ∧
      (∀ k, k ∈ post.accessedStorageKeys ↔ k ∈ devm.accessedStorageKeys) ∧
      (∀ a, a ∈ post.accessedAddresses ↔ a ∈ d1.accessedAddresses) ∧
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
  let child := initEvm (msg.withBenv benv')
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile hbt
    · rfl
    · change sevm.benvStat.rules.isPrecomp dadr = false
      exact h_nonprecompile
  obtain ⟨out, hexec, herr, hout, hgasOut, hworld, hlogsOut, hrefundOut,
    hatdOut, haaOut, haskOut⟩ :=
    callee_exec (msg.withBenv benv') (mcs - 17)
      (by change code = calleeCode; exact h_code)
      (by change mcs = mcs - 17 + 17; omega)
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
  have hd1refund : d1.refundCounter = devm.refundCounter := hd1frame.2.2.1
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
      (by simpa [p, msg] using henter) (by simpa [p, msg] using hres)
  have hpask : p.accessedStorageKeys = devm.accessedStorageKeys := hd1wm.2
  have haskOut' : out.accessedStorageKeys = devm.accessedStorageKeys :=
    haskOut.trans hd1wm.2
  have hpaa : p.accessedAddresses = d1.accessedAddresses := rfl
  have haaOut' : out.accessedAddresses = d1.accessedAddresses := haaOut
  refine ⟨post, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    stmid, ?_, ?_⟩
  · show ((((incorporateChildOnSuccess p out out.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + out.gasLeft⟩).memWrite
        oiw.toNat (out.output.take osw.toNat))).stack = 1 :: s
    rw [Devm.memWrite_stack, Devm.stack_setMach]
    change 1 :: d1.stack = 1 :: s
    rw [hd1stack]
  · show ((((incorporateChildOnSuccess p out out.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + out.gasLeft⟩).memWrite
        oiw.toNat (out.output.take osw.toNat))).memory = _
    rw [Devm.memWrite_memory, Devm.memory_setMach, hout]
    change (d1.memory.extends
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]).write
        oiw.toNat ((1 : B256).toBytes.take osw.toNat) = _
    rw [hd1mem]
  · show ((((incorporateChildOnSuccess p out out.output).setMach
      ⟨1 :: p.stack, p.memory, p.gasLeft + out.gasLeft⟩).memWrite
        oiw.toNat (out.output.take osw.toNat))).gasLeft = _
    rw [Devm.memWrite_gasLeft, Devm.gasLeft_setMach, hgasOut]
    change d1.gasLeft - (mcc + ext) + (mcs - 17) = _
    rfl
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
    rw [show out.transientStorage =
      (initDevm (msg.withBenv benv')).transientStorage from
        congrArg World.transientStorage hworld]
    exact hd1wm.1
  · intro k
    change k ∈ p.accessedStorageKeys.union out.accessedStorageKeys ↔
      k ∈ devm.accessedStorageKeys
    rw [hpask, haskOut']
    exact ⟨fun h => (Std.HashSet.mem_union_iff.mp h).elim id id,
      fun h => Std.HashSet.mem_union_iff.mpr (Or.inl h)⟩
  · intro a
    change a ∈ p.accessedAddresses.union out.accessedAddresses ↔
      a ∈ d1.accessedAddresses
    rw [hpaa, haaOut']
    exact ⟨fun h => (Std.HashSet.mem_union_iff.mp h).elim id id,
      fun h => Std.HashSet.mem_union_iff.mpr (Or.inl h)⟩
  · rw [← hd1state]
    have hsub' : p.state.subBal sevm.currentTarget 0 = some stmid := by
      simpa [msg, staticcallSpawnMsg, callMsg] using hsub
    rw [show p.state = d1.state from rfl] at hsub'
    exact hsub'
  · change out.state = stmid.addBal tw.toAdr 0
    rw [show out.state = (initDevm (msg.withBenv benv')).state from
      congrArg World.state hworld]
    rfl

/-! ## The two witness worlds

One deployment, two entry storages.  Both worlds install the production runtime
at `configWorldOwner` and the responder callee at `pauseWorldCallee`, and both
are entered by the same `pause(0x77)` message from the assigned pauser `9`.
They differ in one dimension only: how many assignments pauser `9` holds.

* **`pauseLastWorldStor`** (row 19, `.pauseLastTargetExpiry`): the Registry
  holds exactly the entry `(0x77, 9)`.  Unregistering the target retires the
  pauser — the decremented count is zero, so `pauseSuccess` takes the
  store-zero arm and clears the pauser's heartbeat expiry.
* **`pauseRetainedWorldStor`** (row 18, `.pauseRetainedTargetExpiry`): a second
  target `t2 = 0x88` is also assigned to pauser `9`.  The decremented count is
  one, so `pauseSuccess` takes the checked arm and writes a fresh expiry from
  the configured heartbeat interval.

`t2` is codeless and never called: only the pause *target* needs an account,
and world 18 deliberately gives `t2` none.

A world is data, not a claim: nothing here is pinned or published, and what is
proved *about* a world is what carries weight. -/

/-- The pausable target being paused: the account carrying the responder
callee.  Not a precompile (`1..17` excluded). -/
def pauseWorldCallee : Adr := Nat.toAdr 0x77

/-- The live pauser making the call, as an address. -/
def pauseWorldPauserAdr : Adr := Nat.toAdr 9

/-- The live pauser, as the storage word its assignments record. -/
def pauseWorldPauser : B256 := 9

/-- World 18's second target: recorded in the Registry, codeless, never
called. -/
def pauseWorldT2 : B256 := 0x88

/-- Block timestamp at the pausing call.  Strictly below the pauser's
heartbeat expiry, so the liveness guard falls through. -/
def pauseWorldTime : B256 := 10

/-- The calling pauser's heartbeat expiry at entry. -/
def pauseWorldExpiry : B256 := 100

/-- The configured heartbeat interval: `officialParams`' own initial value. -/
def pauseWorldInterval : B256 := 2592000

/-- The configured pause duration: `officialParams`' own initial value, which
sits strictly inside the immutable `[432000, 5184000]` bounds — the same
choice `configWorldDuration` makes. -/
def pauseWorldDuration : B256 := 1814400

theorem pauseWorld_pauserAdr_toB256 :
    pauseWorldPauserAdr.toB256 = pauseWorldPauser := by decide

theorem pauseWorld_calleeAdr_toB256 :
    pauseWorldCallee.toB256 = 0x77 := by decide

/-- The pauser is heartbeat-live at the world's timestamp. -/
theorem pauseWorld_time_lt_expiry :
    pauseWorldTime.toNat < pauseWorldExpiry.toNat := by decide

/-- The chosen duration sits inside `officialParams`' immutable bounds, so it
is a value a deployed CircuitBreaker's configuration cell can actually hold. -/
theorem pauseWorldDuration_bounds :
    officialParams.minPauseDuration.toNat ≤ pauseWorldDuration.toNat ∧
      pauseWorldDuration.toNat ≤ officialParams.maxPauseDuration.toNat := by
  exact ⟨by decide, by decide⟩

theorem pauseWorld_calleeValid :
    nonzeroCanonicalAddress pauseWorldCallee.toB256 := by
  refine ⟨by decide, ?_⟩
  show pauseWorldCallee.toB256.toNat < 2 ^ 160
  decide

theorem pauseWorld_t2Valid : nonzeroCanonicalAddress pauseWorldT2 := by
  refine ⟨by decide, ?_⟩
  show pauseWorldT2.toNat < 2 ^ 160
  decide

theorem pauseWorld_pauserValid : nonzeroCanonicalAddress pauseWorldPauser := by
  refine ⟨by decide, ?_⟩
  show pauseWorldPauser.toNat < 2 ^ 160
  decide

/-! ### Slot separation

Every pair among the eleven cells the pause route reads or writes at these
worlds.  All payloads are concrete numerals, so each separation is decided
outright; the region machinery (`slot_ne_of_region_ne`,
`slot_injective_payload`) is reserved for the `_other` lemmas below, whose
keys are variable. -/

theorem pauseWorld_interval_ne_duration :
    heartbeatIntervalSlot ≠ pauseDurationSlot := by decide

theorem pauseWorld_interval_ne_length :
    heartbeatIntervalSlot ≠ arrayLengthSlot := by decide

theorem pauseWorld_interval_ne_entryOne :
    heartbeatIntervalSlot ≠ arrayEntrySlot 1 := by decide

theorem pauseWorld_interval_ne_entryTwo :
    heartbeatIntervalSlot ≠ arrayEntrySlot 2 := by decide

theorem pauseWorld_interval_ne_assignCallee :
    heartbeatIntervalSlot ≠ assignmentSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_interval_ne_assignT2 :
    heartbeatIntervalSlot ≠ assignmentSlot pauseWorldT2 := by decide

theorem pauseWorld_interval_ne_indexCallee :
    heartbeatIntervalSlot ≠ indexSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_interval_ne_indexT2 :
    heartbeatIntervalSlot ≠ indexSlot pauseWorldT2 := by decide

theorem pauseWorld_interval_ne_count :
    heartbeatIntervalSlot ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_interval_ne_expiry :
    heartbeatIntervalSlot ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_duration_ne_length :
    pauseDurationSlot ≠ arrayLengthSlot := by decide

theorem pauseWorld_duration_ne_entryOne :
    pauseDurationSlot ≠ arrayEntrySlot 1 := by decide

theorem pauseWorld_duration_ne_entryTwo :
    pauseDurationSlot ≠ arrayEntrySlot 2 := by decide

theorem pauseWorld_duration_ne_assignCallee :
    pauseDurationSlot ≠ assignmentSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_duration_ne_assignT2 :
    pauseDurationSlot ≠ assignmentSlot pauseWorldT2 := by decide

theorem pauseWorld_duration_ne_indexCallee :
    pauseDurationSlot ≠ indexSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_duration_ne_indexT2 :
    pauseDurationSlot ≠ indexSlot pauseWorldT2 := by decide

theorem pauseWorld_duration_ne_count :
    pauseDurationSlot ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_duration_ne_expiry :
    pauseDurationSlot ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_length_ne_entryOne :
    arrayLengthSlot ≠ arrayEntrySlot 1 := by decide

theorem pauseWorld_length_ne_entryTwo :
    arrayLengthSlot ≠ arrayEntrySlot 2 := by decide

theorem pauseWorld_length_ne_assignCallee :
    arrayLengthSlot ≠ assignmentSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_length_ne_assignT2 :
    arrayLengthSlot ≠ assignmentSlot pauseWorldT2 := by decide

theorem pauseWorld_length_ne_indexCallee :
    arrayLengthSlot ≠ indexSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_length_ne_indexT2 :
    arrayLengthSlot ≠ indexSlot pauseWorldT2 := by decide

theorem pauseWorld_length_ne_count :
    arrayLengthSlot ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_length_ne_expiry :
    arrayLengthSlot ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_entryOne_ne_entryTwo :
    arrayEntrySlot 1 ≠ arrayEntrySlot 2 := by decide

theorem pauseWorld_entryOne_ne_assignCallee :
    arrayEntrySlot 1 ≠ assignmentSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_entryOne_ne_assignT2 :
    arrayEntrySlot 1 ≠ assignmentSlot pauseWorldT2 := by decide

theorem pauseWorld_entryOne_ne_indexCallee :
    arrayEntrySlot 1 ≠ indexSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_entryOne_ne_indexT2 :
    arrayEntrySlot 1 ≠ indexSlot pauseWorldT2 := by decide

theorem pauseWorld_entryOne_ne_count :
    arrayEntrySlot 1 ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_entryOne_ne_expiry :
    arrayEntrySlot 1 ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_entryTwo_ne_assignCallee :
    arrayEntrySlot 2 ≠ assignmentSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_entryTwo_ne_assignT2 :
    arrayEntrySlot 2 ≠ assignmentSlot pauseWorldT2 := by decide

theorem pauseWorld_entryTwo_ne_indexCallee :
    arrayEntrySlot 2 ≠ indexSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_entryTwo_ne_indexT2 :
    arrayEntrySlot 2 ≠ indexSlot pauseWorldT2 := by decide

theorem pauseWorld_entryTwo_ne_count :
    arrayEntrySlot 2 ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_entryTwo_ne_expiry :
    arrayEntrySlot 2 ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_assignCallee_ne_assignT2 :
    assignmentSlot pauseWorldCallee.toB256 ≠ assignmentSlot pauseWorldT2 := by decide

theorem pauseWorld_assignCallee_ne_indexCallee :
    assignmentSlot pauseWorldCallee.toB256 ≠ indexSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_assignCallee_ne_indexT2 :
    assignmentSlot pauseWorldCallee.toB256 ≠ indexSlot pauseWorldT2 := by decide

theorem pauseWorld_assignCallee_ne_count :
    assignmentSlot pauseWorldCallee.toB256 ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_assignCallee_ne_expiry :
    assignmentSlot pauseWorldCallee.toB256 ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_assignT2_ne_indexCallee :
    assignmentSlot pauseWorldT2 ≠ indexSlot pauseWorldCallee.toB256 := by decide

theorem pauseWorld_assignT2_ne_indexT2 :
    assignmentSlot pauseWorldT2 ≠ indexSlot pauseWorldT2 := by decide

theorem pauseWorld_assignT2_ne_count :
    assignmentSlot pauseWorldT2 ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_assignT2_ne_expiry :
    assignmentSlot pauseWorldT2 ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_indexCallee_ne_indexT2 :
    indexSlot pauseWorldCallee.toB256 ≠ indexSlot pauseWorldT2 := by decide

theorem pauseWorld_indexCallee_ne_count :
    indexSlot pauseWorldCallee.toB256 ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_indexCallee_ne_expiry :
    indexSlot pauseWorldCallee.toB256 ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_indexT2_ne_count :
    indexSlot pauseWorldT2 ≠ countSlot pauseWorldPauser := by decide

theorem pauseWorld_indexT2_ne_expiry :
    indexSlot pauseWorldT2 ≠ expirySlot pauseWorldPauser := by decide

theorem pauseWorld_count_ne_expiry :
    countSlot pauseWorldPauser ≠ expirySlot pauseWorldPauser := by decide

private theorem pauseWorld_payload_of_canonical {w : B256}
    (h : canonicalAddress w) : w.toNat < 2 ^ 252 := by
  unfold canonicalAddress at h
  exact lt_trans h (by norm_num)

/-! ### The two entry storages -/

/-- Row 19's entry storage: the configuration cells plus the singleton
Registry `[(0x77, 9)]` — array length `1`, array slot `1`, the target's
assignment and one-based index, the pauser's assignment count `1` — and the
pauser's heartbeat expiry. -/
def pauseLastWorldStor : Stor :=
  Stor.empty
    |>.set heartbeatIntervalSlot pauseWorldInterval
    |>.set pauseDurationSlot pauseWorldDuration
    |>.set arrayLengthSlot 1
    |>.set (arrayEntrySlot 1) pauseWorldCallee.toB256
    |>.set (assignmentSlot pauseWorldCallee.toB256) pauseWorldPauser
    |>.set (indexSlot pauseWorldCallee.toB256) 1
    |>.set (countSlot pauseWorldPauser) 1
    |>.set (expirySlot pauseWorldPauser) pauseWorldExpiry

/-- Row 18's entry storage: the same plus the second entry `(0x88, 9)` —
array length `2`, `t2` in array slot `2` with one-based index `2`, its
assignment to the same pauser, whose count is `2`. -/
def pauseRetainedWorldStor : Stor :=
  Stor.empty
    |>.set heartbeatIntervalSlot pauseWorldInterval
    |>.set pauseDurationSlot pauseWorldDuration
    |>.set arrayLengthSlot 2
    |>.set (arrayEntrySlot 1) pauseWorldCallee.toB256
    |>.set (arrayEntrySlot 2) pauseWorldT2
    |>.set (assignmentSlot pauseWorldCallee.toB256) pauseWorldPauser
    |>.set (assignmentSlot pauseWorldT2) pauseWorldPauser
    |>.set (indexSlot pauseWorldCallee.toB256) 1
    |>.set (indexSlot pauseWorldT2) 2
    |>.set (countSlot pauseWorldPauser) 2
    |>.set (expirySlot pauseWorldPauser) pauseWorldExpiry

/-! ### Row 19's storage, read cell by cell -/

theorem pauseLastStor_interval :
    pauseLastWorldStor.get heartbeatIntervalSlot = pauseWorldInterval := by
  decide

theorem pauseLastStor_duration :
    pauseLastWorldStor.get pauseDurationSlot = pauseWorldDuration := by decide

theorem pauseLastStor_length :
    pauseLastWorldStor.get arrayLengthSlot = 1 := by decide

theorem pauseLastStor_entry :
    pauseLastWorldStor.get (arrayEntrySlot 1) = pauseWorldCallee.toB256 := by
  decide

theorem pauseLastStor_assignment :
    pauseLastWorldStor.get (assignmentSlot pauseWorldCallee.toB256) =
      pauseWorldPauser := by decide

theorem pauseLastStor_index :
    pauseLastWorldStor.get (indexSlot pauseWorldCallee.toB256) = 1 := by
  decide

theorem pauseLastStor_count :
    pauseLastWorldStor.get (countSlot pauseWorldPauser) = 1 := by decide

theorem pauseLastStor_expiry :
    pauseLastWorldStor.get (expirySlot pauseWorldPauser) =
      pauseWorldExpiry := by decide

/-- Every key outside the eight cells row 19's deployment writes reads back
zero. -/
private theorem pauseLastStor_zero {key : B256}
    (hinterval : heartbeatIntervalSlot ≠ key)
    (hduration : pauseDurationSlot ≠ key)
    (hlength : arrayLengthSlot ≠ key)
    (hentry : arrayEntrySlot 1 ≠ key)
    (hassignment : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hindex : indexSlot pauseWorldCallee.toB256 ≠ key)
    (hcount : countSlot pauseWorldPauser ≠ key)
    (hexpiry : expirySlot pauseWorldPauser ≠ key) :
    pauseLastWorldStor.get key = 0 := by
  rw [pauseLastWorldStor, Stor.get_set_ne _ hexpiry, Stor.get_set_ne _ hcount,
    Stor.get_set_ne _ hindex, Stor.get_set_ne _ hassignment,
    Stor.get_set_ne _ hentry, Stor.get_set_ne _ hlength,
    Stor.get_set_ne _ hduration, Stor.get_set_ne _ hinterval]
  simp [Stor.get, Stor.empty]

/-- Every canonical target other than `0x77` is unassigned in row 19's
world. -/
theorem pauseLastStor_assignment_other {t : B256}
    (hcanonical : canonicalAddress t) (hne : t ≠ pauseWorldCallee.toB256) :
    pauseLastWorldStor.get (assignmentSlot t) = 0 := by
  have hp : t.toNat < 2 ^ 252 := pauseWorld_payload_of_canonical hcanonical
  refine pauseLastStor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · intro heq
    exact hne (slot_injective_payload (by decide) (by decide) hp heq).symm
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)

/-- Every canonical target other than `0x77` has a zero reverse index in row
19's world. -/
theorem pauseLastStor_index_other {t : B256}
    (hcanonical : canonicalAddress t) (hne : t ≠ pauseWorldCallee.toB256) :
    pauseLastWorldStor.get (indexSlot t) = 0 := by
  have hp : t.toNat < 2 ^ 252 := pauseWorld_payload_of_canonical hcanonical
  refine pauseLastStor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · intro heq
    exact hne (slot_injective_payload (by decide) (by decide) hp heq).symm
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)

/-- Every canonical pauser other than `9` holds no assignment in row 19's
world. -/
theorem pauseLastStor_count_other {p : B256}
    (hcanonical : canonicalAddress p) (hne : p ≠ pauseWorldPauser) :
    pauseLastWorldStor.get (countSlot p) = 0 := by
  have hp : p.toNat < 2 ^ 252 := pauseWorld_payload_of_canonical hcanonical
  refine pauseLastStor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · intro heq
    exact hne (slot_injective_payload (by decide) (by decide) hp heq).symm
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)

/-- Every canonical pauser other than `9` has a zero heartbeat expiry in row
19's world. -/
theorem pauseLastStor_expiry_other {p : B256}
    (hcanonical : canonicalAddress p) (hne : p ≠ pauseWorldPauser) :
    pauseLastWorldStor.get (expirySlot p) = 0 := by
  have hp : p.toNat < 2 ^ 252 := pauseWorld_payload_of_canonical hcanonical
  refine pauseLastStor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · intro heq
    exact hne (slot_injective_payload (by decide) (by decide) hp heq).symm

/-! ### Row 18's storage, read cell by cell -/

theorem pauseRetainedStor_interval :
    pauseRetainedWorldStor.get heartbeatIntervalSlot =
      pauseWorldInterval := by decide

theorem pauseRetainedStor_duration :
    pauseRetainedWorldStor.get pauseDurationSlot = pauseWorldDuration := by
  decide

theorem pauseRetainedStor_length :
    pauseRetainedWorldStor.get arrayLengthSlot = 2 := by decide

theorem pauseRetainedStor_entryOne :
    pauseRetainedWorldStor.get (arrayEntrySlot 1) =
      pauseWorldCallee.toB256 := by decide

theorem pauseRetainedStor_entryTwo :
    pauseRetainedWorldStor.get (arrayEntrySlot 2) = pauseWorldT2 := by decide

theorem pauseRetainedStor_assignment :
    pauseRetainedWorldStor.get (assignmentSlot pauseWorldCallee.toB256) =
      pauseWorldPauser := by decide

theorem pauseRetainedStor_assignmentT2 :
    pauseRetainedWorldStor.get (assignmentSlot pauseWorldT2) =
      pauseWorldPauser := by decide

theorem pauseRetainedStor_index :
    pauseRetainedWorldStor.get (indexSlot pauseWorldCallee.toB256) = 1 := by
  decide

theorem pauseRetainedStor_indexT2 :
    pauseRetainedWorldStor.get (indexSlot pauseWorldT2) = 2 := by decide

theorem pauseRetainedStor_count :
    pauseRetainedWorldStor.get (countSlot pauseWorldPauser) = 2 := by decide

theorem pauseRetainedStor_expiry :
    pauseRetainedWorldStor.get (expirySlot pauseWorldPauser) =
      pauseWorldExpiry := by decide

/-- Every key outside the eleven cells row 18's deployment writes reads back
zero. -/
private theorem pauseRetainedStor_zero {key : B256}
    (hinterval : heartbeatIntervalSlot ≠ key)
    (hduration : pauseDurationSlot ≠ key)
    (hlength : arrayLengthSlot ≠ key)
    (hentryOne : arrayEntrySlot 1 ≠ key)
    (hentryTwo : arrayEntrySlot 2 ≠ key)
    (hassignment : assignmentSlot pauseWorldCallee.toB256 ≠ key)
    (hassignmentT2 : assignmentSlot pauseWorldT2 ≠ key)
    (hindex : indexSlot pauseWorldCallee.toB256 ≠ key)
    (hindexT2 : indexSlot pauseWorldT2 ≠ key)
    (hcount : countSlot pauseWorldPauser ≠ key)
    (hexpiry : expirySlot pauseWorldPauser ≠ key) :
    pauseRetainedWorldStor.get key = 0 := by
  rw [pauseRetainedWorldStor, Stor.get_set_ne _ hexpiry,
    Stor.get_set_ne _ hcount, Stor.get_set_ne _ hindexT2,
    Stor.get_set_ne _ hindex, Stor.get_set_ne _ hassignmentT2,
    Stor.get_set_ne _ hassignment, Stor.get_set_ne _ hentryTwo,
    Stor.get_set_ne _ hentryOne, Stor.get_set_ne _ hlength,
    Stor.get_set_ne _ hduration, Stor.get_set_ne _ hinterval]
  simp [Stor.get, Stor.empty]

/-- Every canonical target other than `0x77` and `0x88` is unassigned in row
18's world. -/
theorem pauseRetainedStor_assignment_other {t : B256}
    (hcanonical : canonicalAddress t) (hne : t ≠ pauseWorldCallee.toB256)
    (hne2 : t ≠ pauseWorldT2) :
    pauseRetainedWorldStor.get (assignmentSlot t) = 0 := by
  have hp : t.toNat < 2 ^ 252 := pauseWorld_payload_of_canonical hcanonical
  refine pauseRetainedStor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · intro heq
    exact hne (slot_injective_payload (by decide) (by decide) hp heq).symm
  · intro heq
    exact hne2 (slot_injective_payload (by decide) (by decide) hp heq).symm
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)

/-- Every canonical target other than `0x77` and `0x88` has a zero reverse
index in row 18's world. -/
theorem pauseRetainedStor_index_other {t : B256}
    (hcanonical : canonicalAddress t) (hne : t ≠ pauseWorldCallee.toB256)
    (hne2 : t ≠ pauseWorldT2) :
    pauseRetainedWorldStor.get (indexSlot t) = 0 := by
  have hp : t.toNat < 2 ^ 252 := pauseWorld_payload_of_canonical hcanonical
  refine pauseRetainedStor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · intro heq
    exact hne (slot_injective_payload (by decide) (by decide) hp heq).symm
  · intro heq
    exact hne2 (slot_injective_payload (by decide) (by decide) hp heq).symm
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)

/-- Every canonical pauser other than `9` holds no assignment in row 18's
world. -/
theorem pauseRetainedStor_count_other {p : B256}
    (hcanonical : canonicalAddress p) (hne : p ≠ pauseWorldPauser) :
    pauseRetainedWorldStor.get (countSlot p) = 0 := by
  have hp : p.toNat < 2 ^ 252 := pauseWorld_payload_of_canonical hcanonical
  refine pauseRetainedStor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · intro heq
    exact hne (slot_injective_payload (by decide) (by decide) hp heq).symm
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)

/-- Every canonical pauser other than `9` has a zero heartbeat expiry in row
18's world. -/
theorem pauseRetainedStor_expiry_other {p : B256}
    (hcanonical : canonicalAddress p) (hne : p ≠ pauseWorldPauser) :
    pauseRetainedWorldStor.get (expirySlot p) = 0 := by
  have hp : p.toNat < 2 ^ 252 := pauseWorld_payload_of_canonical hcanonical
  refine pauseRetainedStor_zero ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · exact slot_ne_of_region_ne (by decide) (by decide) (by decide) hp
      (by decide)
  · intro heq
    exact hne (slot_injective_payload (by decide) (by decide) hp heq).symm

/-! ### The Registry witnesses

Each entry storage is the image of its ordered entry list under the Registry's
slot layout, so both worlds are Registry-well-formed — unlike
`Blanc/LidoCircuitBreakerReplacementWorld.lean`, whose header documents its own
self-limitation.  As there, a witness is a projection relation, **not** a
reachability claim: no deployment, constructor or prior transaction is
exhibited here. -/

theorem pauseLastStor_witness :
    RegistryWitness (logicalStorageOfStor pauseLastWorldStor)
      [(pauseWorldCallee.toB256, pauseWorldPauser)] := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entry member
    rw [List.mem_singleton] at member
    subst member
    exact pauseWorld_calleeValid
  · intro entry member
    rw [List.mem_singleton] at member
    subst member
    exact pauseWorld_pauserValid
  · show pauseLastWorldStor.get arrayLengthSlot = Nat.toB256 1
    decide
  · intro index bound
    have hzero : index = 0 := by
      simp only [List.length_singleton] at bound
      omega
    subst hzero
    show pauseLastWorldStor.get (arrayEntrySlot (Nat.toB256 1)) =
      targetAt [(pauseWorldCallee.toB256, pauseWorldPauser)] 0
    decide
  · intro t canonical
    show pauseLastWorldStor.get (assignmentSlot t) =
      assignmentAt [(pauseWorldCallee.toB256, pauseWorldPauser)] t
    by_cases ht : t = pauseWorldCallee.toB256
    · subst ht
      decide
    · rw [pauseLastStor_assignment_other canonical ht]
      have hne : pauseWorldCallee.toB256 ≠ t := fun h => ht h.symm
      simp [assignmentAt, hne]
  · intro t canonical
    show pauseLastWorldStor.get (indexSlot t) =
      Nat.toB256 (oneBasedIndexAt
        [(pauseWorldCallee.toB256, pauseWorldPauser)] t)
    by_cases ht : t = pauseWorldCallee.toB256
    · subst ht
      decide
    · rw [pauseLastStor_index_other canonical ht]
      have hne : pauseWorldCallee.toB256 ≠ t := fun h => ht h.symm
      simp only [oneBasedIndexAt, if_neg hne]
      decide
  · intro p canonical
    show pauseLastWorldStor.get (countSlot p) =
      Nat.toB256 (assignmentCount
        [(pauseWorldCallee.toB256, pauseWorldPauser)] p)
    by_cases hp : p = pauseWorldPauser
    · subst hp
      decide
    · rw [pauseLastStor_count_other canonical hp]
      have hne : pauseWorldPauser ≠ p := fun h => hp h.symm
      simp only [assignmentCount, if_neg hne]
      decide
  · show pauseLastWorldStor.get (countSlot 0) = 0
    decide

theorem pauseRetainedStor_witness :
    RegistryWitness (logicalStorageOfStor pauseRetainedWorldStor)
      [(pauseWorldCallee.toB256, pauseWorldPauser),
        (pauseWorldT2, pauseWorldPauser)] := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro entry member
    rcases List.mem_cons.mp member with h | h
    · subst h
      exact pauseWorld_calleeValid
    · rw [List.mem_singleton] at h
      subst h
      exact pauseWorld_t2Valid
  · intro entry member
    rcases List.mem_cons.mp member with h | h
    · subst h
      exact pauseWorld_pauserValid
    · rw [List.mem_singleton] at h
      subst h
      exact pauseWorld_pauserValid
  · show pauseRetainedWorldStor.get arrayLengthSlot = Nat.toB256 2
    decide
  · intro index bound
    rcases index with _ | _ | n
    · decide
    · decide
    · refine absurd bound ?_
      show ¬ (n + 1 + 1 < 2)
      omega
  · intro t canonical
    show pauseRetainedWorldStor.get (assignmentSlot t) =
      assignmentAt [(pauseWorldCallee.toB256, pauseWorldPauser),
        (pauseWorldT2, pauseWorldPauser)] t
    by_cases ht : t = pauseWorldCallee.toB256
    · subst ht
      decide
    · by_cases ht2 : t = pauseWorldT2
      · subst ht2
        decide
      · rw [pauseRetainedStor_assignment_other canonical ht ht2]
        have hne : pauseWorldCallee.toB256 ≠ t := fun h => ht h.symm
        have hne2 : pauseWorldT2 ≠ t := fun h => ht2 h.symm
        simp [assignmentAt, hne, hne2]
  · intro t canonical
    show pauseRetainedWorldStor.get (indexSlot t) =
      Nat.toB256 (oneBasedIndexAt [(pauseWorldCallee.toB256, pauseWorldPauser),
        (pauseWorldT2, pauseWorldPauser)] t)
    by_cases ht : t = pauseWorldCallee.toB256
    · subst ht
      decide
    · by_cases ht2 : t = pauseWorldT2
      · subst ht2
        decide
      · rw [pauseRetainedStor_index_other canonical ht ht2]
        have hne : pauseWorldCallee.toB256 ≠ t := fun h => ht h.symm
        have hne2 : pauseWorldT2 ≠ t := fun h => ht2 h.symm
        simp only [oneBasedIndexAt, if_neg hne, if_neg hne2]
        decide
  · intro p canonical
    show pauseRetainedWorldStor.get (countSlot p) =
      Nat.toB256 (assignmentCount [(pauseWorldCallee.toB256, pauseWorldPauser),
        (pauseWorldT2, pauseWorldPauser)] p)
    by_cases hp : p = pauseWorldPauser
    · subst hp
      decide
    · rw [pauseRetainedStor_count_other canonical hp]
      have hne : pauseWorldPauser ≠ p := fun h => hp h.symm
      simp only [assignmentCount, if_neg hne]
      decide
  · show pauseRetainedWorldStor.get (countSlot 0) = 0
    decide

/-! ### The model-side entry lists

The swap-pop facts a walk composition consumes at each world: the paused
target sits at model index `0`, and removing it leaves the empty Registry
(row 19) or the singleton `[(0x88, 9)]` (row 18). -/

theorem pauseLastWorld_find :
    findEntry [(pauseWorldCallee.toB256, pauseWorldPauser)]
      pauseWorldCallee.toB256 = some (0, pauseWorldPauser) := by decide

theorem pauseLastWorld_swapPop :
    swapPop [(pauseWorldCallee.toB256, pauseWorldPauser)] 0 = [] := by decide

theorem pauseRetainedWorld_find :
    findEntry [(pauseWorldCallee.toB256, pauseWorldPauser),
      (pauseWorldT2, pauseWorldPauser)] pauseWorldCallee.toB256 =
      some (0, pauseWorldPauser) := by decide

theorem pauseRetainedWorld_swapPop :
    swapPop [(pauseWorldCallee.toB256, pauseWorldPauser),
      (pauseWorldT2, pauseWorldPauser)] 0 =
      [(pauseWorldT2, pauseWorldPauser)] := by decide

/-! ### World state: the two accounts

The CircuitBreaker deployment carries the entry storage and the production
runtime; the pause target carries the responder callee.  World 18's second
target `t2` deliberately has **no** account. -/

theorem pauseWorld_callee_ne_owner : pauseWorldCallee ≠ configWorldOwner := by
  decide

theorem pauseWorld_owner_ne_callee : configWorldOwner ≠ pauseWorldCallee := by
  decide

/-- World state: the CircuitBreaker deployment plus the responder callee. -/
def pauseWorldState (stor : Stor) : State :=
  State.set
    (State.set (.empty : State) configWorldOwner
      { Acct.nil with stor := stor, code := configWorldCode })
    pauseWorldCallee { Acct.nil with code := calleeCode }

theorem pauseWorldState_get_breaker (stor : Stor) :
    (pauseWorldState stor).get configWorldOwner =
      { Acct.nil with stor := stor, code := configWorldCode } := by
  rw [pauseWorldState, State.get_set_ne _ pauseWorld_callee_ne_owner,
    State.get_set_self]

theorem pauseWorldState_get_callee (stor : Stor) :
    (pauseWorldState stor).get pauseWorldCallee =
      { Acct.nil with code := calleeCode } := by
  rw [pauseWorldState, State.get_set_self]

/-- What `EXTCODESIZE` and the delegation resolution read at the callee: the
responder bytes. -/
theorem pauseWorldState_calleeCode (stor : Stor) :
    (pauseWorldState stor).getCode pauseWorldCallee = calleeCode := by
  show ((pauseWorldState stor).get pauseWorldCallee).code = calleeCode
  rw [pauseWorldState_get_callee]

/-- The responder account is nonempty code: its `EXTCODESIZE` is `9`. -/
theorem pauseWorld_calleeCodeSize : calleeCode.size = 9 := by decide

/-- The responder bytes are not an EIP-7702 delegation designator, so the
delegation resolution answers `none` at the callee. -/
theorem calleeCode_notDelegation :
    getDelegatedCodeAddress calleeCode = none := by decide

/-- The delegation resolution at any account whose code is not a delegation
designator: no delegation, the account's own code, no extra charge, and an
untouched machine.  This is the exact shape `h_del` takes at a world where
the callee's code is known. -/
lemma accessDelegation_of_none {devm : Devm} {a : Adr}
    (h : getDelegatedCodeAddress (devm.state.getCode a) = none) :
    accessDelegation devm a = ⟨false, a, devm.state.getCode a, 0, devm⟩ := by
  unfold accessDelegation
  simp only [h]

/-! ### The message

`breakerMsg`'s two-account variant: same deployment address, calldata
`pause(0x77)`, caller the assigned pauser, gas **parameterized** — the concrete
numeral is fixed later by the walk composition.  `depth = 1024` (not `0`): the
route's `CALL`/`STATICCALL` spawns need a nonzero remaining depth.  Both
accessed sets start empty — a cold-realistic entry. -/

/-- Canonical direct-call calldata for `pause(0x77)`: thirty-six bytes. -/
def pauseWorldCalldata : Bytes := pauseCalldata pauseWorldCallee.toB256

/-- The concrete pauser `pause(0x77)` call at a parameterized gas. -/
def pauseWorldMsg (stor : Stor) (gas : Nat) : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := pauseWorldState stor
        stat :=
          { (default : BenvStat) with
            origState := pauseWorldState stor
            time := pauseWorldTime } }
    tenv := default
    caller := pauseWorldPauserAdr
    target := some configWorldOwner
    currentTarget := configWorldOwner
    gas := gas
    value := 0
    data := pauseWorldCalldata
    codeAddress := some configWorldOwner
    code := configWorldCode
    depth := 1024
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := false }

/-- The message's symbolic half. -/
def pauseWorldSevm (stor : Stor) (gas : Nat) : Sevm :=
  initSevm (pauseWorldMsg stor gas)

/-- The message's dynamic half at entry: the prestate a run starts from. -/
def pauseWorldPre (stor : Stor) (gas : Nat) : Devm :=
  initDevm (pauseWorldMsg stor gas)

/-! ### Frame-shape facts -/

private theorem pauseWorld_byteArray_ofList_toList (bs : Bytes) :
    (ByteArray.mk bs.toArray).toList = bs := by
  rw [ByteArray.toList_eq_toList_data]

theorem pauseWorld_currentTarget (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).currentTarget = configWorldOwner := rfl

theorem pauseWorld_value (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).value = 0 := rfl

theorem pauseWorld_static (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).isStatic = false := rfl

theorem pauseWorld_codeAddress (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).codeAddress = some configWorldOwner := rfl

theorem pauseWorld_codeAddress_currentTarget (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).codeAddress =
      some (pauseWorldSevm stor gas).currentTarget := rfl

theorem pauseWorld_time (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).benvStat.time = pauseWorldTime := rfl

theorem pauseWorld_caller (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).caller = pauseWorldPauserAdr := rfl

/-- The `CALLER` word the route's guards compare against the target's
assignment cell. -/
theorem pauseWorld_callerWord (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).caller.toB256 = pauseWorldPauser :=
  pauseWorld_pauserAdr_toB256

theorem pauseWorld_depth (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).depth = 1024 := rfl

theorem pauseWorld_gas (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).gas = gas := rfl

theorem pauseWorld_memory (stor : Stor) (gas : Nat) :
    (pauseWorldPre stor gas).memory = Mem.empty := rfl

theorem pauseWorld_logs (stor : Stor) (gas : Nat) :
    (pauseWorldPre stor gas).logs = [] := rfl

/-- Both accessed sets are empty at entry: a cold-realistic start. -/
theorem pauseWorld_accessedStorageKeys (stor : Stor) (gas : Nat) :
    (pauseWorldPre stor gas).accessedStorageKeys =
      Std.HashSet.emptyWithCapacity := rfl

theorem pauseWorld_accessedAddresses (stor : Stor) (gas : Nat) :
    (pauseWorldPre stor gas).accessedAddresses =
      Std.HashSet.emptyWithCapacity := rfl

theorem pauseWorld_codeBytes (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [pauseWorldSevm, pauseWorldMsg, initSevm, configWorldCode] using
    pauseWorld_byteArray_ofList_toList (lidoCircuitBreakerCode officialParams)

/-- The message frame really enters the code frame these worlds are about. -/
theorem pauseWorld_frameEntry (stor : Stor) (gas : Nat) :
    (Frame.ofCall (pauseWorldMsg stor gas)).enter =
      .run ⟨0, pauseWorldSevm stor gas, pauseWorldPre stor gas⟩ := rfl

/-! ### The same facts at the `Msg` itself -/

theorem pauseWorld_msgTarget (stor : Stor) (gas : Nat) :
    (pauseWorldMsg stor gas).target = some configWorldOwner := rfl

theorem pauseWorld_msgOwner (stor : Stor) (gas : Nat) :
    (pauseWorldMsg stor gas).currentTarget = configWorldOwner := rfl

theorem pauseWorld_msgCodeAddress (stor : Stor) (gas : Nat) :
    (pauseWorldMsg stor gas).codeAddress = some configWorldOwner := rfl

theorem pauseWorld_msgValue (stor : Stor) (gas : Nat) :
    (pauseWorldMsg stor gas).value = 0 := rfl

theorem pauseWorld_msgData (stor : Stor) (gas : Nat) :
    (pauseWorldMsg stor gas).data = pauseWorldCalldata := rfl

theorem pauseWorld_msgCode (stor : Stor) (gas : Nat) :
    (pauseWorldMsg stor gas).code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [pauseWorldMsg, configWorldCode] using
    pauseWorld_byteArray_ofList_toList (lidoCircuitBreakerCode officialParams)

/-! ### Calldata staging

`pause(address)` calldata is thirty-six bytes: a four-byte selector and one
head word.  The length, the head word and the selector are settled here once,
before any execution is looked at — the same staging
`Blanc/LidoCircuitBreakerPauseAttainment.lean` performs for its own world. -/

theorem pauseWorld_data (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).data = pauseCalldata pauseWorldCallee.toB256 :=
  rfl

theorem pauseWorld_dataFacts (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).data.length = 36 ∧
      Sevm.argWord (pauseWorldSevm stor gas) 0 = pauseWorldCallee.toB256 :=
  pauseCalldata_facts (pauseWorld_data stor gas)

theorem pauseWorld_dataLength (stor : Stor) (gas : Nat) :
    (pauseWorldSevm stor gas).data.length = 36 :=
  (pauseWorld_dataFacts stor gas).1

theorem pauseWorld_argTarget (stor : Stor) (gas : Nat) :
    Sevm.argWord (pauseWorldSevm stor gas) 0 = pauseWorldCallee.toB256 :=
  (pauseWorld_dataFacts stor gas).2

theorem pauseWorld_dataWord_target (stor : Stor) (gas : Nat) :
    Sevm.dataWord (pauseWorldSevm stor gas) 4 = pauseWorldCallee.toB256 := by
  have h := (pauseWorld_dataFacts stor gas).2
  rw [Sevm.argWord] at h
  rwa [show 32 * (0 : B256) + 4 = 4 from by decide] at h

set_option maxRecDepth 1021 in
/-- The dispatcher's selector at this world's calldata.  Stated at the
concrete target because `Sevm.dataWord` reads a whole word: the selector
occupies the first four bytes and the argument the next twenty-eight of the
same word, and separating them takes an evaluation rather than a lemma. -/
theorem pauseWorld_selector (stor : Stor) (gas : Nat) :
    Sevm.selector (pauseWorldSevm stor gas) =
      selector "pause" [.address] := by
  show Sevm.dataWord (pauseWorldSevm stor gas) 0 >>> 224 = _
  unfold Sevm.dataWord
  rw [pauseWorld_data]
  decide

/-! ### Storage at message entry -/

theorem pauseWorld_getStor (stor : Stor) (gas : Nat) :
    Devm.getStor (pauseWorldPre stor gas) configWorldOwner = stor := by
  change ((pauseWorldState stor).get configWorldOwner).stor = stor
  rw [pauseWorldState_get_breaker]

theorem pauseWorld_getStorVal (stor : Stor) (gas : Nat) {key : B256} :
    (pauseWorldPre stor gas).getStorVal configWorldOwner key =
      stor.get key := by
  change ((pauseWorldState stor).get configWorldOwner).stor.get key = _
  rw [pauseWorldState_get_breaker]

theorem pauseWorld_getOrigStor (stor : Stor) (gas : Nat) {key : B256} :
    getOrigStorVal (pauseWorldSevm stor gas) configWorldOwner key =
      stor.get key := by
  change ((pauseWorldState stor).get configWorldOwner).stor.get key = _
  rw [pauseWorldState_get_breaker]

/-- The callee's code as the entry `Devm` reads it. -/
theorem pauseWorld_calleeCodeAt (stor : Stor) (gas : Nat) :
    (pauseWorldPre stor gas).state.getCode pauseWorldCallee = calleeCode :=
  pauseWorldState_calleeCode stor

/-- Both worlds record the paused target's assignment to the calling
pauser. -/
theorem pauseWorld_lastAssignment (gas : Nat) :
    (pauseWorldPre pauseLastWorldStor gas).getStorVal configWorldOwner
      (assignmentSlot pauseWorldCallee.toB256) = pauseWorldPauser := by
  rw [pauseWorld_getStorVal, pauseLastStor_assignment]

theorem pauseWorld_retainedAssignment (gas : Nat) :
    (pauseWorldPre pauseRetainedWorldStor gas).getStorVal configWorldOwner
      (assignmentSlot pauseWorldCallee.toB256) = pauseWorldPauser := by
  rw [pauseWorld_getStorVal, pauseRetainedStor_assignment]

/-- The Registry witnesses, transported to the two entry prestates. -/
theorem pauseWorld_lastPreWitness (gas : Nat) :
    RegistryWitness
      (logicalStorageOfStor
        (Devm.getStor (pauseWorldPre pauseLastWorldStor gas)
          configWorldOwner))
      [(pauseWorldCallee.toB256, pauseWorldPauser)] := by
  rw [pauseWorld_getStor]
  exact pauseLastStor_witness

theorem pauseWorld_retainedPreWitness (gas : Nat) :
    RegistryWitness
      (logicalStorageOfStor
        (Devm.getStor (pauseWorldPre pauseRetainedWorldStor gas)
          configWorldOwner))
      [(pauseWorldCallee.toB256, pauseWorldPauser),
        (pauseWorldT2, pauseWorldPauser)] := by
  rw [pauseWorld_getStor]
  exact pauseRetainedStor_witness

end Blanc.LidoCircuitBreaker
