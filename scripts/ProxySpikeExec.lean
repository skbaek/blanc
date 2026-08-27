import Blanc.TransientSettlement

/-!
# Spike evidence: an executed `DELEGATECALL` child, and where its writes land

Branch-local evidence for goal `proxy-delegatecall-spike-v1`, row **P2**.
Deliberately outside `Blanc/`: it binds no gate and states no baseline.

`scripts/ProxySpikeSpawn.lean` established the *edge* — what message a
`DELEGATECALL` builds. This file runs the child that message describes and
asks the question the whole spike turns on: **whose storage does the
implementation's `SSTORE` reach?**

The design keeps the answer honest by construction. One parametric execution
fact, `impl_exec`, says what the implementation program does to *any* message
carrying its code; its storage conclusion is stated at `m.currentTarget`,
whatever that is. The two probes below are then the *same* theorem instantiated
at two messages that differ in exactly one field:

* `delcallSpawnMsg` sets `currentTarget := sevm.currentTarget` — the proxy;
* `callSpawnMsg` sets `currentTarget := callee` — the implementation.

So the anti-vacuity control is not a separate argument that could quietly
disagree with the positive result; it is the same argument, and the two land in
different accounts precisely because `proxyAdr ≠ implAdr`.
-/

namespace Blanc.ProxySpikeExec

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## The pair -/

/-- The proxy account: the storage owner under `DELEGATECALL`. -/
def proxyAdr : Adr := 0x00000000000000000000000000000000000a0001

/-- The implementation account: the code address under `DELEGATECALL`. -/
def implAdr : Adr := 0x00000000000000000000000000000000000b0002

/-- The implementation's own storage word. Kept small and distinct from the
three ERC-1967 slots derived in `scripts/ProxySpikeSlots.lean`. -/
def implSlot : B256 := 7

theorem proxyAdr_ne_implAdr : proxyAdr ≠ implAdr := by decide

/-! ## The implementation program

One persistent write, then a returndata-bearing success path: `SSTORE
implSlot 1; MSTORE 0 42; RETURN 0 32`. Fourteen bytes, `.branch`-free, four
constructors, no computed jump. -/

def implMain : Func :=
  pushB256 1 ::: pushB256 implSlot ::: sstore :::
  pushB256 42 ::: mstoreAt 0 +++ pushB256 32 ::: pushB256 0 ::: Func.last .ret

def implProg : Prog := ⟨implMain, []⟩

def implBytes : Bytes := (Prog.compile implProg).getD []

def implCode : ByteArray := ByteArray.mk implBytes.toArray

/-- The returned word, so the returndata clause is stated against a name. -/
def implReturnWord : B256 := 42

theorem implProg_compiles : implProg.compiles = true := by decide

theorem implProg_compile : Prog.compile implProg = some implBytes :=
  Prog.compile_eq_some_getD_of_compiles _ implProg_compiles

/-- Fourteen bytes: `5b 60 01 60 07 55 60 2a 5f 52 60 20 5f f3`. -/
theorem implBytes_length : implBytes.length = 14 := by decide +kernel

/-- Not an EIP-7702 designator, so `accessDelegation` resolves to the identity
on this account and the probe is not accidentally testing 7702. -/
theorem implCode_notDelegation : getDelegatedCodeAddress implCode = none := by
  decide +kernel


/-! ## The body's charge, as a named sum

`implMain`'s eight instructions, grouped as they are written: the `SSTORE` and
its two argument pushes, the `MSTORE` and its two, the `RETURN`'s two.  The
`SSTORE` is charged **cold** (`gasColdSload`) and in the *set* value case
(`gasStorageSet`), which is what `implMain_runCompiledTo`'s `h_cold`, `h_orig`
and `h_cur` premises pin down; `RETURN` reads a window the `MSTORE` already
paid to open, so it adds nothing. -/

def implBodyGas : Nat :=
  (gVerylow + gVerylow + (gasColdSload + gasStorageSet))
    + (gVerylow + gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

/-- 22122 gas, of which 22100 is the one cold `SSTORE` into a zero slot. -/
theorem implBodyGas_eq : implBodyGas = 22122 := by decide

/-- The whole message's charge: the body plus the `JUMPDEST` every compiled
`Prog` enters through. -/
def implEntryGas : Nat := implBodyGas + gJumpdest

theorem implEntryGas_eq : implEntryGas = 22123 := by decide

/-! ## Projections off the persistent column

`Devm.getStorVal` reads `devm.world.state` and nothing else, so every update
the tail of `implMain` performs after the `SSTORE` — the `MSTORE`'s image, the
`RETURN`'s read-back and output — is invisible to it.  Bridging that with a
bare `rfl` over the concrete post-state tower is what the
`devm-projection-bridge` recipe forbids; these are the update-first Jaune
projection lemmas for the columns this walk actually moves, each stated one
layer deep over a variable. -/

/-- The `RETURN` post-state's world is the world the frame had reached:
`setMach`, `memRead` and `withOutput` all move machine or meta columns only.
Stated one layer deep over a *variable* state, which is what keeps the concrete
walk term out of the bridge. -/
private lemma retPost_world (d : Devm) (S : List B256) (G i sz : Nat)
    (out : Bytes) :
    ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput out).world
      = d.world := rfl

/-- Storage reads only through the persistent state, so a state equation
transports every one of them. -/
private lemma getStorVal_congr {d d' : Devm} (h : d.state = d'.state)
    (a : Adr) (k : B256) : d.getStorVal a k = d'.getStorVal a k := by
  unfold Devm.getStorVal Devm.getAcct
  rw [h]

/-- Reading a storage word out of the `RETURN` post-state: it is the word the
frame's persistent state already carried. -/
private lemma retPost_getStorVal (d : Devm) (S : List B256) (G i sz : Nat)
    (out : Bytes) (a : Adr) (k : B256) :
    ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput
      out).getStorVal a k = d.getStorVal a k :=
  getStorVal_congr
    (show _ = _ from congrArg World.state (retPost_world d S G i sz out)) a k

private lemma retPost_transientStorage (d : Devm) (S : List B256) (G i sz : Nat)
    (out : Bytes) :
    ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput
      out).transientStorage = d.transientStorage :=
  congrArg World.transientStorage (retPost_world d S G i sz out)

/-! ### The `SSTORE` successor's storage column

`func_run`'s cold `SSTORE` arm builds its successor as `setStorVal` over
`withRefundCounter` over `addAccessedStorageKey`.  Only the outermost of those
three touches storage; the two below it are meta-column updates with their own
Jaune/Blanc projection laws. -/

private lemma getStorVal_setStorVal_self (d : Devm) (a : Adr) (k v : B256) :
    (d.setStorVal a k v).getStorVal a k = v := by
  show (Devm.getStor (d.setStorVal a k v) a).get k = v
  rw [setStorVal_getStor_self, Stor.get_set_self]

private lemma getStorVal_setStorVal_ne (d : Devm) {a a' : Adr} {k k' : B256}
    {v : B256} (h : (a', k') ≠ (a, k)) :
    (d.setStorVal a k v).getStorVal a' k' = d.getStorVal a' k' := by
  by_cases hadr : a = a'
  · subst hadr
    have hkey : k ≠ k' := fun hk => h (by rw [hk])
    show (Devm.getStor (d.setStorVal a k v) a).get k' = _
    rw [setStorVal_getStor_self, Stor.get_set_ne _ hkey]
    rfl
  · show (Devm.getStor (d.setStorVal a k v) a').get k' = _
    have hoff : Devm.getStor (d.setStorVal a k v) a' = Devm.getStor d a' := by
      simp only [Devm.getStor, Devm.getAcct, Devm.setStorVal, Devm.withState,
        Devm.setWorld, State.setStorVal]
      simp only [Devm.state, State.get_set_ne _ hadr]
    rw [hoff]
    rfl

private lemma sstoreBase_getStorVal (d : Devm) (t : Adr) (key : B256) (rc : Int)
    (a : Adr) (k : B256) :
    ((addAccessedStorageKey d t key).withRefundCounter rc).getStorVal a k
      = d.getStorVal a k := by
  show (Devm.getStor _ a).get k = (Devm.getStor d a).get k
  rw [Devm.withRefundCounter_getStor, addAccessedStorageKey_getStor]

private lemma sstoreBase_transientStorage (d : Devm) (t : Adr) (key : B256)
    (rc : Int) (v : B256) :
    (((addAccessedStorageKey d t key).withRefundCounter rc).setStorVal t key
      v).transientStorage = d.transientStorage := rfl

private lemma sstoreBase_logs (d : Devm) (t : Adr) (key : B256)
    (rc : Int) (v : B256) :
    (((addAccessedStorageKey d t key).withRefundCounter rc).setStorVal t key
      v).logs = d.logs := rfl

private lemma sstoreBase_error (d : Devm) (t : Adr) (key : B256)
    (rc : Int) (v : B256) :
    (((addAccessedStorageKey d t key).withRefundCounter rc).setStorVal t key
      v).error = d.error := rfl

/-! ## The implementation's own walk

The `Blanc/LidoCircuitBreakerPauseWorld.lean` responder walk with one `SSTORE`
put in front of the `MSTORE`/`RETURN` tail.  The three storage premises are
exactly what that instruction's forward rule needs and no more:

* `h_cold` chooses the cold arm of `Ninst.runCompiled_sstore_cold` — the key
  joins the accessed set here, so the charge carries `gasColdSload`;
* `h_orig` and `h_cur` are what make the value case the *set* case:
  `sstoreValueCost` charges `gasStorageSet` exactly when the original and
  current words agree and differ from the new one, and `1` differs from `0`.
  Without them the charge is a variable and no exact gas figure exists;
* `h_static` is `SSTORE`'s own static-context sentry.

None of the three is vacuous: a fresh frame over an untouched zero slot
satisfies all of them at once, which is precisely the world the two probes
below instantiate. -/

theorem implMain_runCompiledTo (fs : List Func) (sevm : Sevm) (base : Devm)
    (G : Nat) (h_static : sevm.isStatic = false)
    (h_cold : (⟨sevm.currentTarget, implSlot⟩ : Adr × B256)
      ∉ base.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal base sevm.currentTarget implSlot = 0) :
    ∃ post,
      Func.RunCompiledTo fs sevm (base.setMach ⟨[], Mem.empty, G + implBodyGas⟩)
        implMain (.ok post) ∧
      post.error = base.error ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget implSlot = 1 ∧
      (∀ a k, (a, k) ≠ (sevm.currentTarget, implSlot) →
        Devm.getStorVal post a k = Devm.getStorVal base a k) ∧
      post.transientStorage = base.transientStorage ∧
      post.logs = base.logs := by
  apply Exists.intro
  refine ⟨?walk, ?herr, ?hout, ?hgas, ?hstor, ?hframe, ?htra, ?hlogs⟩
  case walk =>
    rw [implBodyGas_eq]
    unfold implMain mstoreAt
    func_run [22100, 3]
    case h_cost =>
      rw [Devm.getStorVal_setMach, h_orig, h_cur]
      decide
    case h_ext =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide]
      exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_ret_word (i := 0) (sz := 32) (s := [])
        (e := 0) (G := G) (out := (42 : B256).toBytes)
      · rfl
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide,
          show ((0 : B256) * 32).toNat = 0 by decide]
        exact Devm.extCost_word_word Mem.size_write_word
      · show G + 22122 - 22122 = G + 0
        omega
      · rw [show ((0 : B256)).toNat = 0 by decide,
          show ((32 : B256)).toNat = 32 by decide]
        exact Devm.memRead_word_fst
          (by rw [show ((0 : B256) * 32).toNat = 0 by decide]; rfl)
  case herr =>
    rw [Devm.withOutput_error, Devm.memRead_error, Devm.setMach_error,
      Devm.setMach_error, sstoreBase_error, Devm.setMach_error]
  case hout => rfl
  case hgas => rfl
  case hstor =>
    rw [retPost_getStorVal, Devm.getStorVal_setMach, getStorVal_setStorVal_self]
  case hframe =>
    intro a k hne
    rw [retPost_getStorVal, Devm.getStorVal_setMach,
      getStorVal_setStorVal_ne _ hne, sstoreBase_getStorVal,
      Devm.getStorVal_setMach]
  case htra =>
    rw [retPost_transientStorage, Devm.setMach_transientStorage,
      sstoreBase_transientStorage, Devm.setMach_transientStorage]
  case hlogs =>
    rw [Devm.withOutput_logs, Devm.memRead_logs, Devm.setMach_logs,
      Devm.setMach_logs, sstoreBase_logs, Devm.setMach_logs]


/-! ## The total execution, parametric in the message

`Blanc/LidoCircuitBreakerPauseWorld.lean`'s `callee_exec` with the storage
conclusions added.  Every one of them is stated at **`m.currentTarget`** — the
message's storage owner — and at no fixed address, which is the whole design:
the two probes below are this one theorem instantiated at two messages that
differ in that field and in nothing else that matters here. -/

theorem impl_exec (m : Msg) (G : Nat)
    (hcode : m.code = implCode)
    (hgas : m.gas = G + implEntryGas)
    (h_static : m.isStatic = false)
    (h_cold : (⟨m.currentTarget, implSlot⟩ : Adr × B256)
      ∉ m.accessedStorageKeys)
    (h_orig : getOrigStorVal (initSevm m) m.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal (initDevm m) m.currentTarget implSlot = 0) :
    ∃ post,
      exec (initEvm m) = .ok post ∧
      post.error = none ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = G ∧
      Devm.getStorVal post m.currentTarget implSlot = 1 ∧
      (∀ a k, (a, k) ≠ (m.currentTarget, implSlot) →
        Devm.getStorVal post a k = Devm.getStorVal (initDevm m) a k) ∧
      post.transientStorage = (initDevm m).transientStorage ∧
      post.logs = [] := by
  obtain ⟨post, walk, herr, hout, hgasPost, hstor, hframe, htra, hlogs⟩ :=
    implMain_runCompiledTo [implMain] (initSevm m) (initDevm m) G h_static
      h_cold h_orig h_cur
  refine ⟨post, ?_, by rw [herr]; rfl, hout, hgasPost, hstor, hframe, htra,
    by rw [hlogs]; rfl⟩
  have hrun : Prog.RunCompiledTo (initSevm m) (initDevm m) implProg
      (.ok post) := by
    refine Prog.runCompiledTo_intro (G := G + implBodyGas)
      (mid := (initDevm m).setMach ⟨[], Mem.empty, G + implBodyGas⟩) ?_ rfl walk
    show m.gas = G + implBodyGas + gJumpdest
    rw [hgas]
    simp only [implEntryGas]
    omega
  have hcompile : some (initSevm m).code.toList = Prog.compile implProg := by
    show some m.code.toList = _
    rw [hcode, implProg_compile]
    simp [implCode, ByteArray.toList_eq_toList_data]
  exact Prog.exec_of_runCompiledTo hrun hcompile


/-! ## The message an actual `DELEGATECALL` builds

`scripts/ProxySpikeSpawn.lean` proves — in `Blanc.ProxySpike.directDelcall_spawn`
— that a `DELEGATECALL` edge spawns `Blanc.ProxySpike.delcallSpawnMsg`.  Files
under `scripts/` cannot import one another, so the constructor is restated here
character for character; the two are the same term, and the probe below is
therefore about the message the opcode actually builds rather than about a
message chosen to make the theorem come out. -/

/-- The message a `DELEGATECALL` builds.  Copied verbatim from
`Blanc.ProxySpike.delcallSpawnMsg` in `scripts/ProxySpikeSpawn.lean`. -/
def delcallChildMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (codeAdr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs sevm.value sevm.caller sevm.currentTarget codeAdr
    false false (p.memory.data.sliceD ii is 0) code dp

private lemma implAdr_key_ne_proxy :
    ((implAdr, implSlot) : Adr × B256) ≠ (proxyAdr, implSlot) :=
  fun h => proxyAdr_ne_implAdr (congrArg Prod.fst h).symm

private lemma proxyAdr_key_ne_impl :
    ((proxyAdr, implSlot) : Adr × B256) ≠ (implAdr, implSlot) :=
  fun h => proxyAdr_ne_implAdr (congrArg Prod.fst h)

/-! ## The positive probe: under `DELEGATECALL` the write lands in the proxy

`impl_exec` instantiated at `delcallChildMsg`.  Nothing here is special-cased:
the storage conclusion is the parametric one, and it names the proxy only
because `delcallSpawnMsg` puts `sevm.currentTarget` in the storage-owner slot
while putting `implAdr` in the code-address slot. -/

theorem delcall_child_writes_proxy_storage
    (sevm : Sevm) (p : Devm) (ii is : Nat) (dp : Bool) (G : Nat)
    (h_target : sevm.currentTarget = proxyAdr)
    (h_static : sevm.isStatic = false)
    (h_cold : (⟨proxyAdr, implSlot⟩ : Adr × B256) ∉ p.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm proxyAdr implSlot = 0)
    (h_cur : Devm.getStorVal p proxyAdr implSlot = 0) :
    ∃ post,
      exec (initEvm (delcallChildMsg sevm p (G + implEntryGas) implAdr ii is
        implCode dp)) = .ok post ∧
      post.error = none ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = G ∧
      Devm.getStorVal post proxyAdr implSlot = 1 ∧
      Devm.getStorVal post implAdr implSlot =
        Devm.getStorVal (initDevm (delcallChildMsg sevm p (G + implEntryGas)
          implAdr ii is implCode dp)) implAdr implSlot := by
  obtain ⟨post, hexec, herr, hout, hgas, hstor, hframe, _, _⟩ :=
    impl_exec (delcallChildMsg sevm p (G + implEntryGas) implAdr ii is
      implCode dp) G rfl rfl
      (by show (false || sevm.isStatic) = false; rw [Bool.false_or, h_static])
      (by
        show (⟨sevm.currentTarget, implSlot⟩ : Adr × B256)
          ∉ p.accessedStorageKeys
        rw [h_target]; exact h_cold)
      (by show getOrigStorVal sevm sevm.currentTarget implSlot = 0
          rw [h_target]; exact h_orig)
      (by show Devm.getStorVal p sevm.currentTarget implSlot = 0
          rw [h_target]; exact h_cur)
  refine ⟨post, hexec, herr, hout, hgas, ?_, ?_⟩
  · show Devm.getStorVal post proxyAdr implSlot = 1
    rw [← h_target]; exact hstor
  · refine hframe implAdr implSlot ?_
    show ((implAdr, implSlot) : Adr × B256) ≠ (sevm.currentTarget, implSlot)
    rw [h_target]; exact implAdr_key_ne_proxy

/-! ## The anti-vacuity control: under `CALL` the write lands in the callee

The same theorem at `Blanc.callSpawnMsg`, whose storage-owner and code-address
slots take the *same* address.  This is not a separate argument that could
quietly disagree with the one above; it is `impl_exec` again, and the only
thing that changed is the message's `currentTarget`. -/

theorem control_call_child_writes_callee_storage
    (sevm : Sevm) (p : Devm) (ii is : Nat) (dp : Bool) (G : Nat)
    (h_static : sevm.isStatic = false)
    (h_cold : (⟨implAdr, implSlot⟩ : Adr × B256) ∉ p.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm implAdr implSlot = 0)
    (h_cur : Devm.getStorVal p implAdr implSlot = 0) :
    ∃ post,
      exec (initEvm (callSpawnMsg sevm p (G + implEntryGas) implAdr ii is
        implCode dp)) = .ok post ∧
      post.error = none ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = G ∧
      Devm.getStorVal post implAdr implSlot = 1 ∧
      Devm.getStorVal post proxyAdr implSlot =
        Devm.getStorVal (initDevm (callSpawnMsg sevm p (G + implEntryGas)
          implAdr ii is implCode dp)) proxyAdr implSlot := by
  obtain ⟨post, hexec, herr, hout, hgas, hstor, hframe, _, _⟩ :=
    impl_exec (callSpawnMsg sevm p (G + implEntryGas) implAdr ii is
      implCode dp) G rfl rfl
      (by show (false || sevm.isStatic) = false; rw [Bool.false_or, h_static])
      h_cold h_orig h_cur
  exact ⟨post, hexec, herr, hout, hgas, hstor,
    hframe proxyAdr implSlot proxyAdr_key_ne_impl⟩

/-! ## The two probes land in different accounts

The control bites only if it disagrees with the positive result, so this states
the disagreement outright: the *same* implementation code, entered from the
*same* parent state with the *same* gas, writes `implSlot` in the proxy under
`DELEGATECALL` and in the implementation under `CALL`, and leaves the other
account's word at the `0` it entered with.  `proxyAdr ≠ implAdr` is what makes
those two sentences say different things. -/

theorem delcall_and_call_write_different_accounts
    (sevm : Sevm) (p : Devm) (ii is : Nat) (dp : Bool) (G : Nat)
    (h_target : sevm.currentTarget = proxyAdr)
    (h_static : sevm.isStatic = false)
    (h_cold_proxy : (⟨proxyAdr, implSlot⟩ : Adr × B256) ∉ p.accessedStorageKeys)
    (h_cold_impl : (⟨implAdr, implSlot⟩ : Adr × B256) ∉ p.accessedStorageKeys)
    (h_orig_proxy : getOrigStorVal sevm proxyAdr implSlot = 0)
    (h_orig_impl : getOrigStorVal sevm implAdr implSlot = 0)
    (h_cur_proxy : Devm.getStorVal p proxyAdr implSlot = 0)
    (h_cur_impl : Devm.getStorVal p implAdr implSlot = 0) :
    ∃ dpost cpost,
      exec (initEvm (delcallChildMsg sevm p (G + implEntryGas) implAdr ii is
        implCode dp)) = .ok dpost ∧
      exec (initEvm (callSpawnMsg sevm p (G + implEntryGas) implAdr ii is
        implCode dp)) = .ok cpost ∧
      Devm.getStorVal dpost proxyAdr implSlot = 1 ∧
      Devm.getStorVal dpost implAdr implSlot = 0 ∧
      Devm.getStorVal cpost implAdr implSlot = 1 ∧
      Devm.getStorVal cpost proxyAdr implSlot = 0 ∧
      proxyAdr ≠ implAdr := by
  obtain ⟨dpost, hdexec, _, _, _, hdproxy, hdimpl⟩ :=
    delcall_child_writes_proxy_storage sevm p ii is dp G h_target h_static
      h_cold_proxy h_orig_proxy h_cur_proxy
  obtain ⟨cpost, hcexec, _, _, _, hcimpl, hcproxy⟩ :=
    control_call_child_writes_callee_storage sevm p ii is dp G h_static
      h_cold_impl h_orig_impl h_cur_impl
  exact ⟨dpost, cpost, hdexec, hcexec, hdproxy,
    hdimpl.trans h_cur_impl, hcimpl, hcproxy.trans h_cur_proxy,
    proxyAdr_ne_implAdr⟩


/-! ## Transient storage under `DELEGATECALL`

Jaune keys `TSTORE` on `sevm.currentTarget` — the *identical* expression
`SSTORE` uses (`Jaune/Machine.lean`, the `.sstore` and `.tstore` arms of
`Rinst.runCore`) — so the ownership question has the same answer for the
transient column, and this section proves it rather than asserting it.

Two things differ from the persistent case, and both make this side *simpler*:
`TSTORE` has no warmth and no value cases, so its charge is the flat
`gasWarmAccess` and the walk needs no `h_cold`/`h_orig`/`h_cur`; and
`func_run` has no `TSTORE` arm, so the walk is split around one hand-applied
step. -/

/-! ### `Tra` read-back laws

`Blanc/TransientSettlement.lean` proves these, but privately, so they are not
in scope here.  Restated with the same proofs; `scripts/` evidence may not
reach into an imported module's private section. -/

private theorem tra_getD_set_self (tra : Tra) (a : Adr) (s : Stor) :
    (tra.set a s).getD a .empty = s := by
  unfold Tra.set
  split
  · rw [Std.TreeMap.getD_erase]
    have hcmp : compare a a = Ordering.eq := compare_eq_iff_eq.mpr rfl
    rw [hcmp]
    exact (Std.TreeMap.eq_empty_iff_isEmpty.mpr (by assumption)).symm
  · rw [Std.TreeMap.getD_insert]
    simp

private theorem tra_get_set_self (tra : Tra) (a : Adr) (k v : B256) :
    ((tra.setStorVal a k v).getD a .empty).get k = v := by
  rw [Tra.setStorVal, tra_getD_set_self]
  exact Stor.get_set_self _ _ _

private theorem tra_get_set_same_address (tra : Tra) (a : Adr)
    {k j : B256} (hkj : k ≠ j) (v : B256) :
    ((tra.setStorVal a k v).getD a .empty).get j =
      (tra.getD a .empty).get j := by
  rw [Tra.setStorVal, tra_getD_set_self]
  exact Stor.get_set_ne _ hkj v

private theorem tra_get_set_other_address (tra : Tra)
    {a b : Adr} (hab : a ≠ b) (k v j : B256) :
    ((tra.setStorVal a k v).getD b .empty).get j =
      (tra.getD b .empty).get j := by
  simp only [Tra.setStorVal, Tra.set]
  split
  · rw [Std.TreeMap.getD_erase]
    have hcmp : compare a b ≠ Ordering.eq := by
      intro h
      exact hab (compare_eq_iff_eq.mp h)
    simp [hcmp]
  · rw [Std.TreeMap.getD_insert]
    have hcmp : compare a b ≠ Ordering.eq := by
      intro h
      exact hab (compare_eq_iff_eq.mp h)
    simp [hcmp]

private lemma getTransVal_setTransVal_self (d : Devm) (a : Adr) (k v : B256) :
    (d.setTransVal a k v).getTransVal a k = v :=
  tra_get_set_self d.transientStorage a k v

private lemma getTransVal_setTransVal_ne (d : Devm) {a b : Adr} {k j v : B256}
    (h : (b, j) ≠ (a, k)) :
    (d.setTransVal a k v).getTransVal b j = d.getTransVal b j := by
  by_cases hab : a = b
  · subst hab
    exact tra_get_set_same_address _ _ (fun hk => h (by rw [hk])) _
  · exact tra_get_set_other_address _ hab _ _ _

private lemma getTransVal_setMach (d : Devm) (m : Mach) (a : Adr) (k : B256) :
    (d.setMach m).getTransVal a k = d.getTransVal a k := rfl

private lemma setTransVal_state (d : Devm) (a : Adr) (k v : B256) :
    (d.setTransVal a k v).state = d.state := rfl

private lemma setTransVal_logs (d : Devm) (a : Adr) (k v : B256) :
    (d.setTransVal a k v).logs = d.logs := rfl

private lemma setTransVal_error (d : Devm) (a : Adr) (k v : B256) :
    (d.setTransVal a k v).error = d.error := rfl

private lemma retPost_getTransVal (d : Devm) (S : List B256) (G i sz : Nat)
    (out : Bytes) (a : Adr) (k : B256) :
    ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput
      out).getTransVal a k = d.getTransVal a k := by
  show ((_ : Tra).getD a .empty).get k = _
  rw [retPost_transientStorage]
  rfl

private lemma retPost_state (d : Devm) (S : List B256) (G i sz : Nat)
    (out : Bytes) :
    ((((d.setMach ⟨S, d.memory, G⟩).memRead i sz).2).withOutput out).state
      = d.state :=
  congrArg World.state (retPost_world d S G i sz out)

/-! ### The `TSTORE` step

`Blanc/LidoCircuitBreakerPauseWalk.lean`'s `runCompiled_tstore_of`, restated
here because that module is far above this file's import closure, and with the
successor's `setTransVal`/`setMach` order swapped so that `func_run` can resume
from it: the walk parses a state by its outermost `setMach`. -/

private theorem runCompiled_tstore_of {sevm : Sevm} {pre : Devm}
    {key value : B256} {stack : List B256} {M : Mem} {G : Nat}
    (hstack : pre.stack = key :: value :: stack)
    (hstatic : sevm.isStatic = false)
    (hmem : pre.memory = M)
    (hgas : pre.gasLeft = G + gasWarmAccess) :
    Ninst.RunCompiled sevm pre Ninst.tstore
      ((pre.setTransVal sevm.currentTarget key value).setMach
        ⟨stack, M, G⟩) := by
  subst hmem
  refine Ninst.runCompiled_reg (by rintro ⟨⟩) ?_
  show (do
    let ⟨k, d⟩ ← pre.pop
    let ⟨v, d⟩ ← d.pop
    let d ← chargeGas gasWarmAccess d
    assertDynamic sevm d
    .ok (d.setTransVal sevm.currentTarget k v)) = _
  rw [Devm.pop_eq_ok hstack]
  simp only [bind, Except.bind]
  rw [Devm.pop_eq_ok
    (devm := pre.setMach ⟨value :: stack, pre.memory, pre.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [chargeGas_eq_ok
    (devm := pre.setMach ⟨stack, pre.memory, pre.gasLeft⟩) (by
      simp only [Devm.gasLeft_setMach]
      omega)]
  have hremaining : pre.gasLeft - gasWarmAccess = G := by omega
  simp only [Devm.setMach_setMach,
    Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [hremaining]
  simp [assertDynamic, Except.assert, hstatic]
  rfl

/-! ### The transient implementation program

`implMain` with its one `SSTORE` replaced by a `TSTORE`; fourteen bytes again,
`5b 60 01 60 07 5d 60 2a 5f 52 60 20 5f f3`. -/

def implTransMain : Func :=
  pushB256 1 ::: pushB256 implSlot ::: tstore :::
  pushB256 42 ::: mstoreAt 0 +++ pushB256 32 ::: pushB256 0 ::: Func.last .ret

def implTransProg : Prog := ⟨implTransMain, []⟩

def implTransBytes : Bytes := (Prog.compile implTransProg).getD []

def implTransCode : ByteArray := ByteArray.mk implTransBytes.toArray

theorem implTransProg_compiles : implTransProg.compiles = true := by decide

theorem implTransProg_compile :
    Prog.compile implTransProg = some implTransBytes :=
  Prog.compile_eq_some_getD_of_compiles _ implTransProg_compiles

theorem implTransBytes_length : implTransBytes.length = 14 := by decide +kernel

/-- `TSTORE` has neither a warmth arm nor value cases, so its whole charge is
the flat `gasWarmAccess`; the rest of the body is `implBodyGas`'s. -/
def implTransBodyGas : Nat :=
  (gVerylow + gVerylow + gasWarmAccess)
    + (gVerylow + gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

theorem implTransBodyGas_eq : implTransBodyGas = 122 := by decide

def implTransEntryGas : Nat := implTransBodyGas + gJumpdest

theorem implTransEntryGas_eq : implTransEntryGas = 123 := by decide

/-- The transient body's walk.  Only one premise, `h_static`: `TSTORE`'s sole
guard is the static-context check. -/
theorem implTransMain_runCompiledTo (fs : List Func) (sevm : Sevm) (base : Devm)
    (G : Nat) (h_static : sevm.isStatic = false) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + implTransBodyGas⟩)
        implTransMain (.ok post) ∧
      post.error = base.error ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = G ∧
      Devm.getTransVal post sevm.currentTarget implSlot = 1 ∧
      (∀ a k, (a, k) ≠ (sevm.currentTarget, implSlot) →
        Devm.getTransVal post a k = Devm.getTransVal base a k) ∧
      post.state = base.state ∧
      post.logs = base.logs := by
  apply Exists.intro
  refine ⟨?walk, ?herr, ?hout, ?hgas, ?htrans, ?hframe, ?hstate, ?hlogs⟩
  case walk =>
    rw [implTransBodyGas_eq]
    unfold implTransMain mstoreAt
    func_run (2)
    refine Func.RunCompiledTo.next
      (runCompiled_tstore_of (G := G + 16) rfl h_static rfl
        (by simp only [Devm.gasLeft_setMach, gasWarmAccess]; omega)) ?_
    func_run [3]
    case h_ext =>
      rw [show ((0 : B256) * 32).toNat = 0 by decide]
      exact Devm.extCost_empty_word
    case a =>
      apply Func.runCompiledTo_ret_word (i := 0) (sz := 32) (s := [])
        (e := 0) (G := G) (out := (42 : B256).toBytes)
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
  case herr =>
    rw [Devm.withOutput_error, Devm.memRead_error, Devm.setMach_error,
      Devm.setMach_error, setTransVal_error, Devm.setMach_error]
  case hout => rfl
  case hgas => rfl
  case htrans =>
    rw [retPost_getTransVal, getTransVal_setMach, getTransVal_setTransVal_self]
  case hframe =>
    intro a k hne
    rw [retPost_getTransVal, getTransVal_setMach,
      getTransVal_setTransVal_ne _ hne, getTransVal_setMach]
  case hstate =>
    rw [retPost_state, Devm.setMach_state, setTransVal_state,
      Devm.setMach_state]
  case hlogs =>
    rw [Devm.withOutput_logs, Devm.memRead_logs, Devm.setMach_logs,
      Devm.setMach_logs, setTransVal_logs, Devm.setMach_logs]

/-- The transient body's total execution, again parametric in the message and
again with every cell conclusion stated at `m.currentTarget`. -/
theorem implTrans_exec (m : Msg) (G : Nat)
    (hcode : m.code = implTransCode)
    (hgas : m.gas = G + implTransEntryGas)
    (h_static : m.isStatic = false) :
    ∃ post,
      exec (initEvm m) = .ok post ∧
      post.error = none ∧
      post.output = implReturnWord.toBytes ∧
      post.gasLeft = G ∧
      Devm.getTransVal post m.currentTarget implSlot = 1 ∧
      (∀ a k, (a, k) ≠ (m.currentTarget, implSlot) →
        Devm.getTransVal post a k = Devm.getTransVal (initDevm m) a k) ∧
      post.state = (initDevm m).state ∧
      post.logs = [] := by
  obtain ⟨post, walk, herr, hout, hgasPost, htrans, hframe, hstate, hlogs⟩ :=
    implTransMain_runCompiledTo [implTransMain] (initSevm m) (initDevm m) G
      h_static
  refine ⟨post, ?_, by rw [herr]; rfl, hout, hgasPost, htrans, hframe, hstate,
    by rw [hlogs]; rfl⟩
  have hrun : Prog.RunCompiledTo (initSevm m) (initDevm m) implTransProg
      (.ok post) := by
    refine Prog.runCompiledTo_intro (G := G + implTransBodyGas)
      (mid := (initDevm m).setMach ⟨[], Mem.empty, G + implTransBodyGas⟩) ?_ rfl
      walk
    show m.gas = G + implTransBodyGas + gJumpdest
    rw [hgas]
    simp only [implTransEntryGas]
    omega
  have hcompile :
      some (initSevm m).code.toList = Prog.compile implTransProg := by
    show some m.code.toList = _
    rw [hcode, implTransProg_compile]
    simp [implTransCode, ByteArray.toList_eq_toList_data]
  exact Prog.exec_of_runCompiledTo hrun hcompile

/-- **Positive probe, transient column.**  Under `DELEGATECALL` the transient
cell the implementation writes belongs to the *proxy*. -/
theorem delcall_child_writes_proxy_transient
    (sevm : Sevm) (p : Devm) (ii is : Nat) (dp : Bool) (G : Nat)
    (h_target : sevm.currentTarget = proxyAdr)
    (h_static : sevm.isStatic = false) :
    ∃ post,
      exec (initEvm (delcallChildMsg sevm p (G + implTransEntryGas) implAdr ii
        is implTransCode dp)) = .ok post ∧
      post.error = none ∧
      post.gasLeft = G ∧
      Devm.getTransVal post proxyAdr implSlot = 1 ∧
      Devm.getTransVal post implAdr implSlot = Devm.getTransVal p implAdr
        implSlot := by
  obtain ⟨post, hexec, herr, _, hgas, htrans, hframe, _, _⟩ :=
    implTrans_exec (delcallChildMsg sevm p (G + implTransEntryGas) implAdr ii is
      implTransCode dp) G rfl rfl
      (by show (false || sevm.isStatic) = false; rw [Bool.false_or, h_static])
  refine ⟨post, hexec, herr, hgas, ?_, ?_⟩
  · show Devm.getTransVal post proxyAdr implSlot = 1
    rw [← h_target]; exact htrans
  · refine hframe implAdr implSlot ?_
    show ((implAdr, implSlot) : Adr × B256) ≠ (sevm.currentTarget, implSlot)
    rw [h_target]; exact implAdr_key_ne_proxy

/-- **Anti-vacuity control, transient column.**  Under `CALL` the same cell
belongs to the callee. -/
theorem control_call_child_writes_callee_transient
    (sevm : Sevm) (p : Devm) (ii is : Nat) (dp : Bool) (G : Nat)
    (h_static : sevm.isStatic = false) :
    ∃ post,
      exec (initEvm (callSpawnMsg sevm p (G + implTransEntryGas) implAdr ii is
        implTransCode dp)) = .ok post ∧
      post.error = none ∧
      post.gasLeft = G ∧
      Devm.getTransVal post implAdr implSlot = 1 ∧
      Devm.getTransVal post proxyAdr implSlot = Devm.getTransVal p proxyAdr
        implSlot := by
  obtain ⟨post, hexec, herr, _, hgas, htrans, hframe, _, _⟩ :=
    implTrans_exec (callSpawnMsg sevm p (G + implTransEntryGas) implAdr ii is
      implTransCode dp) G rfl rfl
      (by show (false || sevm.isStatic) = false; rw [Bool.false_or, h_static])
  exact ⟨post, hexec, herr, hgas, htrans,
    hframe proxyAdr implSlot proxyAdr_key_ne_impl⟩

/-- The transient column's own separation statement: the same `TSTORE`, run
from the same parent state, lands in two different accounts depending only on
which opcode spawned the child. -/
theorem delcall_and_call_write_different_transient_accounts
    (sevm : Sevm) (p : Devm) (ii is : Nat) (dp : Bool) (G : Nat)
    (h_target : sevm.currentTarget = proxyAdr)
    (h_static : sevm.isStatic = false)
    (h_cur_proxy : Devm.getTransVal p proxyAdr implSlot = 0)
    (h_cur_impl : Devm.getTransVal p implAdr implSlot = 0) :
    ∃ dpost cpost,
      exec (initEvm (delcallChildMsg sevm p (G + implTransEntryGas) implAdr ii
        is implTransCode dp)) = .ok dpost ∧
      exec (initEvm (callSpawnMsg sevm p (G + implTransEntryGas) implAdr ii is
        implTransCode dp)) = .ok cpost ∧
      Devm.getTransVal dpost proxyAdr implSlot = 1 ∧
      Devm.getTransVal dpost implAdr implSlot = 0 ∧
      Devm.getTransVal cpost implAdr implSlot = 1 ∧
      Devm.getTransVal cpost proxyAdr implSlot = 0 ∧
      proxyAdr ≠ implAdr := by
  obtain ⟨dpost, hdexec, _, _, hdproxy, hdimpl⟩ :=
    delcall_child_writes_proxy_transient sevm p ii is dp G h_target h_static
  obtain ⟨cpost, hcexec, _, _, hcimpl, hcproxy⟩ :=
    control_call_child_writes_callee_transient sevm p ii is dp G h_static
  exact ⟨dpost, cpost, hdexec, hcexec, hdproxy, hdimpl.trans h_cur_impl,
    hcimpl, hcproxy.trans h_cur_proxy, proxyAdr_ne_implAdr⟩

/-! ## The revert path

A third implementation body: the same cold `SSTORE`, then `Func.rev`
(`PUSH0; PUSH0; REVERT`).  What the spike wants from it is that the write the
frame really performed is *undone* when the child settles, and that the parent
sees a `0` status word.

The boundary this stops at is deliberate.  `Frame.enter` — the step that turns
a message into a running `Evm`, past the value transfer and the precompile
table — is a premise of the parent-side crossing lemma
(`Blanc.ProxySpike.Ninst.runCompiled_delcall_doneFrame`'s `h_enter`), not
something this file establishes; so every statement below is about
`(Frame.ofCall m).settle (exec (initEvm m))` and `Resume.run`, which are exactly
the two terms that crossing lemma consumes. -/

def implRevMain : Func :=
  pushB256 1 ::: pushB256 implSlot ::: sstore ::: Func.rev

def implRevProg : Prog := ⟨implRevMain, []⟩

def implRevBytes : Bytes := (Prog.compile implRevProg).getD []

def implRevCode : ByteArray := ByteArray.mk implRevBytes.toArray

theorem implRevProg_compiles : implRevProg.compiles = true := by decide

theorem implRevProg_compile : Prog.compile implRevProg = some implRevBytes :=
  Prog.compile_eq_some_getD_of_compiles _ implRevProg_compiles

/-- Nine bytes: `5b 60 01 60 07 55 5f 5f fd`. -/
theorem implRevBytes_length : implRevBytes.length = 9 := by decide +kernel

def implRevBodyGas : Nat :=
  (gVerylow + gVerylow + (gasColdSload + gasStorageSet)) + (gBase + gBase)

theorem implRevBodyGas_eq : implRevBodyGas = 22110 := by decide

def implRevEntryGas : Nat := implRevBodyGas + gJumpdest

theorem implRevEntryGas_eq : implRevEntryGas = 22111 := by decide

private lemma withOutput_setMach_getStorVal (d : Devm) (m : Mach) (out : Bytes)
    (a : Adr) (k : B256) :
    ((d.setMach m).withOutput out).getStorVal a k = d.getStorVal a k :=
  getStorVal_congr (by rw [Devm.withOutput_state, Devm.setMach_state]) a k

/-- The reverting body's walk.  The `= 1` clause is what stops the rollback
statements below from being vacuous: the frame really did write the slot before
it reverted. -/
theorem implRevMain_runCompiledTo (fs : List Func) (sevm : Sevm) (base : Devm)
    (G : Nat) (h_static : sevm.isStatic = false)
    (h_cold : (⟨sevm.currentTarget, implSlot⟩ : Adr × B256)
      ∉ base.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm sevm.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal base sevm.currentTarget implSlot = 0) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + implRevBodyGas⟩)
        implRevMain (.error (.revert, post)) ∧
      post.output = [] ∧
      post.gasLeft = G ∧
      Devm.getStorVal post sevm.currentTarget implSlot = 1 := by
  apply Exists.intro
  refine ⟨?walk, ?hout, ?hgas, ?hstor⟩
  case walk =>
    rw [implRevBodyGas_eq]
    unfold implRevMain
    func_run [22100]
    case h_cost =>
      rw [Devm.getStorVal_setMach, h_orig, h_cur]
      decide
    case a =>
      exact Func.runCompiledTo_rev_of (i := 0) (sz := 0) (s := []) (G := G)
        rfl Devm.extCost_empty_window (by show G + 22110 - 22110 = G + 0; omega)
        Devm.memRead_zero
  case hout => rfl
  case hgas => rfl
  case hstor =>
    rw [withOutput_setMach_getStorVal, Devm.getStorVal_setMach,
      getStorVal_setStorVal_self]

/-- The reverting body's total execution. -/
theorem implRev_exec (m : Msg) (G : Nat)
    (hcode : m.code = implRevCode)
    (hgas : m.gas = G + implRevEntryGas)
    (h_static : m.isStatic = false)
    (h_cold : (⟨m.currentTarget, implSlot⟩ : Adr × B256)
      ∉ m.accessedStorageKeys)
    (h_orig : getOrigStorVal (initSevm m) m.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal (initDevm m) m.currentTarget implSlot = 0) :
    ∃ post,
      exec (initEvm m) = .error (.revert, post) ∧
      post.output = [] ∧
      post.gasLeft = G ∧
      Devm.getStorVal post m.currentTarget implSlot = 1 := by
  obtain ⟨post, walk, hout, hgasPost, hstor⟩ :=
    implRevMain_runCompiledTo [implRevMain] (initSevm m) (initDevm m) G
      h_static h_cold h_orig h_cur
  refine ⟨post, ?_, hout, hgasPost, hstor⟩
  have hrun : Prog.RunCompiledTo (initSevm m) (initDevm m) implRevProg
      (.error (.revert, post)) := by
    refine Prog.runCompiledTo_intro (G := G + implRevBodyGas)
      (mid := (initDevm m).setMach ⟨[], Mem.empty, G + implRevBodyGas⟩) ?_ rfl
      walk
    show m.gas = G + implRevBodyGas + gJumpdest
    rw [hgas]
    simp only [implRevEntryGas]
    omega
  have hcompile : some (initSevm m).code.toList = Prog.compile implRevProg := by
    show some m.code.toList = _
    rw [hcode, implRevProg_compile]
    simp [implRevCode, ByteArray.toList_eq_toList_data]
  exact Prog.exec_of_runCompiledTo hrun hcompile

/-- **The child's settlement rolls the write back.**  `Frame.settle` on a call
frame is `processMessage.settle`, whose error arm is `Devm.rollback` to the
message's own entry world; so the settled child's persistent state *is* its
message-entry state, and the slot reads whatever it read before the call. -/
theorem implRev_child_settles_rolled_back (m : Msg) (G : Nat)
    (hcode : m.code = implRevCode)
    (hgas : m.gas = G + implRevEntryGas)
    (h_static : m.isStatic = false)
    (h_cold : (⟨m.currentTarget, implSlot⟩ : Adr × B256)
      ∉ m.accessedStorageKeys)
    (h_orig : getOrigStorVal (initSevm m) m.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal (initDevm m) m.currentTarget implSlot = 0) :
    ∃ child,
      (Frame.ofCall m).settle (exec (initEvm m)) = .ok child ∧
      child.error = some .revert ∧
      child.output = [] ∧
      child.gasLeft = G ∧
      child.state = m.benv.state ∧
      child.transientStorage = m.tenv.transientStorage ∧
      Devm.getStorVal child m.currentTarget implSlot
        = Devm.getStorVal (initDevm m) m.currentTarget implSlot := by
  obtain ⟨post, hexec, hout, hgasPost, _⟩ :=
    implRev_exec m G hcode hgas h_static h_cold h_orig h_cur
  refine ⟨(post.withError (some .revert)).rollback m.benv.state
      m.tenv.transientStorage, ?_, rfl, hout, hgasPost, rfl, rfl,
    getStorVal_congr rfl m.currentTarget implSlot⟩
  show Frame.settleMsg (Frame.ofCall m)
    (executeCode.handleError (exec (initEvm m))) = _
  rw [hexec]
  rfl

/-- **The parent sees `0`.**  `Resume.run_call_err` at the settled child: the
CALL-family return pushes the failure flag, keeps the parent's own logs, and
installs the child's rolled-back world. -/
theorem implRev_parent_status_word_zero (m : Msg) (G : Nat) (parent : Devm)
    (oi os : Nat)
    (hcode : m.code = implRevCode)
    (hgas : m.gas = G + implRevEntryGas)
    (h_static : m.isStatic = false)
    (h_cold : (⟨m.currentTarget, implSlot⟩ : Adr × B256)
      ∉ m.accessedStorageKeys)
    (h_orig : getOrigStorVal (initSevm m) m.currentTarget implSlot = 0)
    (h_cur : Devm.getStorVal (initDevm m) m.currentTarget implSlot = 0)
    (h_room : parent.stack.length < 1024) :
    ∃ child resumed,
      (Frame.ofCall m).settle (exec (initEvm m)) = .ok child ∧
      Resume.run (.call parent oi os) (.ok child) = .ok resumed ∧
      resumed.stack = 0 :: parent.stack ∧
      resumed.state = m.benv.state ∧
      resumed.transientStorage = m.tenv.transientStorage ∧
      Devm.getStorVal child m.currentTarget implSlot
        = Devm.getStorVal (initDevm m) m.currentTarget implSlot ∧
      Devm.getStorVal resumed m.currentTarget implSlot
        = Devm.getStorVal (initDevm m) m.currentTarget implSlot := by
  obtain ⟨child, hsettle, herr, hout, _, hstate, htra, hstor⟩ :=
    implRev_child_settles_rolled_back m G hcode hgas h_static h_cold h_orig
      h_cur
  have herrSome : child.error.isSome = true := by rw [herr]; rfl
  have hres := Resume.run_call_err (parent := parent) (oi := oi) (os := os)
    herrSome h_room
  refine ⟨child, _, hsettle, hres, ?_, ?_, ?_, hstor, ?_⟩
  · rw [hout, List.take_nil, Devm.memWrite_nil]
    rfl
  · exact (Resume.call_state hres).trans hstate
  · exact (Resume.call_transientStorage hres).trans htra
  · exact (getStorVal_congr (Resume.call_state hres) m.currentTarget
      implSlot).trans hstor

/-- **The headline for the revert path.**  Under `DELEGATECALL`, a reverting
implementation leaves the *proxy's* slot at the value it entered with, and the
parent's status word is `0`. -/
theorem delcall_revert_restores_proxy_storage
    (sevm : Sevm) (p : Devm) (ii is : Nat) (dp : Bool) (G : Nat)
    (parent : Devm) (oi os : Nat)
    (h_target : sevm.currentTarget = proxyAdr)
    (h_static : sevm.isStatic = false)
    (h_cold : (⟨proxyAdr, implSlot⟩ : Adr × B256) ∉ p.accessedStorageKeys)
    (h_orig : getOrigStorVal sevm proxyAdr implSlot = 0)
    (h_cur : Devm.getStorVal p proxyAdr implSlot = 0)
    (h_room : parent.stack.length < 1024) :
    ∃ child resumed,
      (Frame.ofCall (delcallChildMsg sevm p (G + implRevEntryGas) implAdr ii is
        implRevCode dp)).settle
          (exec (initEvm (delcallChildMsg sevm p (G + implRevEntryGas) implAdr
            ii is implRevCode dp))) = .ok child ∧
      Resume.run (.call parent oi os) (.ok child) = .ok resumed ∧
      Devm.getStorVal child proxyAdr implSlot = 0 ∧
      Devm.getStorVal resumed proxyAdr implSlot = 0 ∧
      resumed.stack = 0 :: parent.stack := by
  have h_static' : (delcallChildMsg sevm p (G + implRevEntryGas) implAdr ii is
      implRevCode dp).isStatic = false := by
    show (false || sevm.isStatic) = false
    rw [Bool.false_or, h_static]
  have h_cold' : (⟨(delcallChildMsg sevm p (G + implRevEntryGas) implAdr ii is
      implRevCode dp).currentTarget, implSlot⟩ : Adr × B256)
      ∉ (delcallChildMsg sevm p (G + implRevEntryGas) implAdr ii is
        implRevCode dp).accessedStorageKeys := by
    show (⟨sevm.currentTarget, implSlot⟩ : Adr × B256) ∉ p.accessedStorageKeys
    rw [h_target]; exact h_cold
  have h_orig' : getOrigStorVal (initSevm (delcallChildMsg sevm p
      (G + implRevEntryGas) implAdr ii is implRevCode dp))
      (delcallChildMsg sevm p (G + implRevEntryGas) implAdr ii is implRevCode
        dp).currentTarget implSlot = 0 := by
    show getOrigStorVal sevm sevm.currentTarget implSlot = 0
    rw [h_target]; exact h_orig
  have h_cur' : Devm.getStorVal (initDevm (delcallChildMsg sevm p
      (G + implRevEntryGas) implAdr ii is implRevCode dp))
      (delcallChildMsg sevm p (G + implRevEntryGas) implAdr ii is implRevCode
        dp).currentTarget implSlot = 0 := by
    show Devm.getStorVal p sevm.currentTarget implSlot = 0
    rw [h_target]; exact h_cur
  obtain ⟨child, resumed, hsettle, hres, hstack, _, _, hchild, hstor⟩ :=
    implRev_parent_status_word_zero
      (delcallChildMsg sevm p (G + implRevEntryGas) implAdr ii is implRevCode
        dp) G parent oi os rfl rfl h_static' h_cold' h_orig' h_cur' h_room
  refine ⟨child, resumed, hsettle, hres, ?_, ?_, hstack⟩
  · rw [← h_target]; exact hchild.trans h_cur'
  · rw [← h_target]; exact hstor.trans h_cur'

/-! ## Non-vacuity: the probes have a model

Every probe above is conditional, and a conditional theorem whose premises are
unsatisfiable says nothing at all.  Jaune's own `Inhabited` frame is a model of
all of them at once — empty persistent state, empty transient storage, empty
accessed-key set, non-static — so the separation results hold of a real frame
and not merely of a hypothetical one. -/

/-- The `Inhabited` frame, moved onto the proxy. -/
def freshSevm : Sevm := { (default : Sevm) with currentTarget := proxyAdr }

theorem freshSevm_satisfies_probe_premises :
    freshSevm.currentTarget = proxyAdr ∧
      freshSevm.isStatic = false ∧
      (⟨proxyAdr, implSlot⟩ : Adr × B256)
        ∉ (default : Devm).accessedStorageKeys ∧
      (⟨implAdr, implSlot⟩ : Adr × B256)
        ∉ (default : Devm).accessedStorageKeys ∧
      getOrigStorVal freshSevm proxyAdr implSlot = 0 ∧
      getOrigStorVal freshSevm implAdr implSlot = 0 ∧
      Devm.getStorVal (default : Devm) proxyAdr implSlot = 0 ∧
      Devm.getStorVal (default : Devm) implAdr implSlot = 0 ∧
      Devm.getTransVal (default : Devm) proxyAdr implSlot = 0 ∧
      Devm.getTransVal (default : Devm) implAdr implSlot = 0 := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩ <;>
    · show _ ∉ (Std.HashSet.emptyWithCapacity : Std.HashSet (Adr × B256))
      simp

/-- The persistent-column separation, unconditionally, at that frame. -/
theorem fresh_delcall_and_call_write_different_accounts (G : Nat) :
    ∃ dpost cpost,
      exec (initEvm (delcallChildMsg freshSevm default (G + implEntryGas)
        implAdr 0 0 implCode false)) = .ok dpost ∧
      exec (initEvm (callSpawnMsg freshSevm default (G + implEntryGas) implAdr
        0 0 implCode false)) = .ok cpost ∧
      Devm.getStorVal dpost proxyAdr implSlot = 1 ∧
      Devm.getStorVal dpost implAdr implSlot = 0 ∧
      Devm.getStorVal cpost implAdr implSlot = 1 ∧
      Devm.getStorVal cpost proxyAdr implSlot = 0 ∧
      proxyAdr ≠ implAdr :=
  have h := freshSevm_satisfies_probe_premises
  delcall_and_call_write_different_accounts freshSevm default 0 0 false G
    h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1

/-- The transient-column separation, unconditionally, at that frame. -/
theorem fresh_delcall_and_call_write_different_transient_accounts (G : Nat) :
    ∃ dpost cpost,
      exec (initEvm (delcallChildMsg freshSevm default (G + implTransEntryGas)
        implAdr 0 0 implTransCode false)) = .ok dpost ∧
      exec (initEvm (callSpawnMsg freshSevm default (G + implTransEntryGas)
        implAdr 0 0 implTransCode false)) = .ok cpost ∧
      Devm.getTransVal dpost proxyAdr implSlot = 1 ∧
      Devm.getTransVal dpost implAdr implSlot = 0 ∧
      Devm.getTransVal cpost implAdr implSlot = 1 ∧
      Devm.getTransVal cpost proxyAdr implSlot = 0 ∧
      proxyAdr ≠ implAdr :=
  have h := freshSevm_satisfies_probe_premises
  delcall_and_call_write_different_transient_accounts freshSevm default 0 0
    false G h.1 h.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2

/-- And the revert path, unconditionally: the write the frame performed is gone
from the proxy when the child settles, and the parent's status word is `0`. -/
theorem fresh_delcall_revert_restores_proxy_storage (G : Nat) :
    ∃ child resumed,
      (Frame.ofCall (delcallChildMsg freshSevm default (G + implRevEntryGas)
        implAdr 0 0 implRevCode false)).settle
          (exec (initEvm (delcallChildMsg freshSevm default
            (G + implRevEntryGas) implAdr 0 0 implRevCode false)))
        = .ok child ∧
      Resume.run (.call default 0 0) (.ok child) = .ok resumed ∧
      Devm.getStorVal child proxyAdr implSlot = 0 ∧
      Devm.getStorVal resumed proxyAdr implSlot = 0 ∧
      resumed.stack = 0 :: (default : Devm).stack :=
  have h := freshSevm_satisfies_probe_premises
  delcall_revert_restores_proxy_storage freshSevm default 0 0 false G default
    0 0 h.1 h.2.1 h.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.1 (by decide)

/-! ## Axiom audit -/

#print axioms implProg_compiles
#print axioms implProg_compile
#print axioms implBytes_length
#print axioms implCode_notDelegation
#print axioms proxyAdr_ne_implAdr
#print axioms implBodyGas_eq
#print axioms implEntryGas_eq
#print axioms implMain_runCompiledTo
#print axioms impl_exec
#print axioms delcall_child_writes_proxy_storage
#print axioms control_call_child_writes_callee_storage
#print axioms delcall_and_call_write_different_accounts
#print axioms implTransProg_compiles
#print axioms implTransProg_compile
#print axioms implTransBytes_length
#print axioms implTransBodyGas_eq
#print axioms implTransEntryGas_eq
#print axioms implTransMain_runCompiledTo
#print axioms implTrans_exec
#print axioms delcall_child_writes_proxy_transient
#print axioms control_call_child_writes_callee_transient
#print axioms delcall_and_call_write_different_transient_accounts
#print axioms implRevProg_compiles
#print axioms implRevProg_compile
#print axioms implRevBytes_length
#print axioms implRevBodyGas_eq
#print axioms implRevEntryGas_eq
#print axioms implRevMain_runCompiledTo
#print axioms implRev_exec
#print axioms implRev_child_settles_rolled_back
#print axioms implRev_parent_status_word_zero
#print axioms delcall_revert_restores_proxy_storage
#print axioms freshSevm_satisfies_probe_premises
#print axioms fresh_delcall_and_call_write_different_accounts
#print axioms fresh_delcall_and_call_write_different_transient_accounts
#print axioms fresh_delcall_revert_restores_proxy_storage


/-! ### The private helpers, audited too

An earlier draft printed axioms only for the public theorems.  A private lemma
reachable from nothing would have been invisible to that audit, so every
declaration this file states is listed. -/

#print axioms retPost_world
#print axioms getStorVal_congr
#print axioms retPost_getStorVal
#print axioms retPost_transientStorage
#print axioms getStorVal_setStorVal_self
#print axioms getStorVal_setStorVal_ne
#print axioms sstoreBase_getStorVal
#print axioms sstoreBase_transientStorage
#print axioms sstoreBase_logs
#print axioms sstoreBase_error
#print axioms implAdr_key_ne_proxy
#print axioms proxyAdr_key_ne_impl
#print axioms tra_getD_set_self
#print axioms tra_get_set_self
#print axioms tra_get_set_same_address
#print axioms tra_get_set_other_address
#print axioms getTransVal_setTransVal_self
#print axioms getTransVal_setTransVal_ne
#print axioms getTransVal_setMach
#print axioms setTransVal_state
#print axioms setTransVal_logs
#print axioms setTransVal_error
#print axioms retPost_getTransVal
#print axioms retPost_state
#print axioms runCompiled_tstore_of
#print axioms withOutput_setMach_getStorVal

end Blanc.ProxySpikeExec
