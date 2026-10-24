import Blanc.ExecutionCellProvenance
import Blanc.ExecutionInRawNodes
import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionOccurrence
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTraceCodeAt

/-!
# Cell provenance at message and transaction level (L1-L2)

`Blanc/ExecutionCellProvenance.lean` proves cell provenance for one `Exec`
run (L0); this module lifts it to retained messages (L1) and selected
transactions (L2), each relative to an arbitrary entry world.

Every `…cellProv_at` lemma takes the entry cell as an explicit value `init`
with an equation `hentry` against its own entry world, so each message arm
(and the transaction) can supply its own bridge: the call arm enters the
resolved execution message, the create arm enters the prepared inner
message, the transaction enters its prepared message. Node cells are read
from the nodes' own devms, exactly as in L0. Every `…cellProv_post` lemma
concludes `CellProv` over the carrier's full `rawNodes`, ending at the
carrier's post cell; the post is chosen so that L2's post is the next
level's init.

Reused (not copied): `Exec.rawNodes_cellProv_noStateGas` and
`CellProv.of_replayCell` with `mono_left`/`trans` (`ExecutionCellProvenance`);
`ProcessMessage.storageReplay_of_body` and
`ProcessCreateMessage.storageReplay_of_body` with
`Exec.storageReplay_committedPost_noStateGas` (`ExecutionOccurrence`);
`benvAfterTransfer_getStor_eq`, `messageCallDelegation_getStor_eq`,
`messageCallExecutionMessage_getStor_eq` (`ExecutionMessageEffects`);
`messageCallExecutionMessage_getCode`, `processCreateMessage.msg_getCode`
(`ExecutionTraceCodeAt`); the three `processMessageCall_*_out_noStateGas`
(`ExecutionHistoricalAdmission`); `TransactionTrace.debitState_getStor_eq`,
`foldl_destroyAccount_get_eq` (`ExecutionTransactionEffects`);
`MessageCallTrace.noDel_of_safe` (`ExecutionNoDelSafeHistory`);
`sweepTouchedAccounts_getStor_of_nonempty`, `payRewards_getStor` is not
needed until L5; `prepareMessage_benv` (`LadderBase`);
`ne_wa_of_not_hasCodeOrNonce` (`CommonProofs`).
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Entering a frame preserves the storage of a code-bearing owner: the
storage twin of `Frame.enter_run_getCode`, via the entry transfer. -/
theorem Frame.enter_run_getStor {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) (a : Adr)
    (hcode : (f.inner.benv.state.getCode a).toList ≠ []) :
    cevm.dyna.getStor a = f.inner.benv.state.getStor a := by
  obtain ⟨benv, hbenv, rfl⟩ := Frame.enter_run_inv h
  exact benvAfterTransfer_ok_getStor hbenv a
    (Or.inr (State.Protected.of_code_ne_nil hcode))

/-- A CREATE frame enters the prepared inner message, whose storage away
from the target is the outer message's storage. -/
theorem createEntry_getStor {msg : Msg} {wa : Adr}
    (htargetNe : msg.currentTarget ≠ wa) :
    (Frame.ofCreate msg).inner.benv.state.getStor wa =
      msg.benv.state.getStor wa := by
  have hinner : (Frame.ofCreate msg).inner = processCreateMessage.msg msg :=
    rfl
  rw [hinner]
  dsimp only [processCreateMessage.msg, Msg.withBenv, Benv.incrNonce,
    Benv.clearStorageWritesIfEmpty, addCreatedAccount, Benv.setStor,
    State.getStor]
  rw [State.incrNonce_get_stor]
  split_ifs with hcond
  · exact absurd hcond.1 htargetNe
  · rw [State.setStor_get_stor_ne htargetNe]

/-- One balance credit keeps a code-bearing owner's storage, via the public
`getStor_addBal` equation. -/
theorem addBal_getStor_of_codenonempty {s : State} {b : Adr} {v : B256}
    {a : Adr} (h : (s.getCode a).toList ≠ []) :
    (s.addBal b v).getStor a = s.getStor a := by
  have hp := State.Protected.of_code_ne_nil h
  rw [getStor_addBal]
  split_ifs with hcond
  · obtain ⟨rfl, hE⟩ := hcond
    rcases hp with hn | hc
    · exact (hn hE.2.1).elim
    · exact (hc hE.1).elim
  · rfl

/-- The deletion fold keeps the storage of an account it never names, via
the public whole-account equation. -/
theorem foldl_destroyAccount_getStor {ca : Adr} {state : State}
    {addresses : List Adr}
    (hne : ∀ address ∈ addresses, address ≠ ca) :
    (addresses.foldl destroyAccount state).getStor ca =
      state.getStor ca := by
  have hget := foldl_destroyAccount_get_eq (ca := ca) (state := state)
    (addresses := addresses) hne
  unfold State.getStor
  exact congrArg Acct.stor hget

/-- Every raw node of a retained slot inherits cell provenance from the
entry world of the frame the slot runs: the `CellProv` analogue of
`RetainedXlot.codeImage_of_safe_entry`, stated with the entry cell equation
so each message arm can supply its own. -/
theorem RetainedXlot.cellProv_at {slot : Xlot}
    (retained : RetainedXlot slot)
    {frame : Frame} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (hrun : RunFrame frame slot out) (k : B256)
    (hsg : frame.inner.benv.stat.rules.stateGas = Option.none)
    {wa : Adr} {C : ByteArray}
    (hC : frame.inner.benv.state.getCode wa = C)
    (hCne : C.toList ≠ [])
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : retained.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((frame.inner.benv.state.getStor wa).get k)) :
    CellProv wa k init before ((n.devm.getStor wa).get k) := by
  cases retained with
  | none =>
      simp only [RetainedXlot.rawNodes] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hstat : sevm.benvStat = frame.inner.benv.stat := by
        have e := Frame.enter_run_benvStat henter
        dsimp only at e
        exact e
      have hsg' : sevm.benvStat.rules.stateGas = Option.none := by
        rw [hstat]
        exact hsg
      have hpreCode : pre.getCode wa = C :=
        (Frame.enter_run_getCode henter wa).trans hC
      have hpreStor : (pre.getStor wa).get k =
          ((frame.inner.benv.state.getStor wa).get k) := by
        exact congrArg (fun storage : Stor => storage.get k)
          (Frame.enter_run_getStor henter wa (by rw [hC]; exact hCne))
      simp only [RetainedXlot.rawNodes] at hsplit
      have hprov := Exec.rawNodes_cellProv_noStateGas run k hsg' hpreCode
        hCne hsplit
      rw [hpreStor, ← hentry] at hprov
      exact hprov

/-- A retained call message inherits cell provenance from its frame entry
world, which is the message's own world. -/
theorem ProcessMessageTrace.cellProv_at {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = Option.none)
    {wa : Adr} {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ [])
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((msg.benv.state.getStor wa).get k)) :
    CellProv wa k init before ((n.devm.getStor wa).get k) :=
  trace.retained.cellProv_at trace.run k hsg hC hCne hsplit hentry

/-- A retained CREATE message inherits cell provenance from its frame entry
world, the prepared inner message's world: away from the target, entry
storage and code are the outer message's. -/
theorem ProcessCreateMessageTrace.cellProv_at {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = Option.none)
    {wa : Adr} {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ [])
    (htargetNe : msg.currentTarget ≠ wa)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((msg.benv.state.getStor wa).get k)) :
    CellProv wa k init before ((n.devm.getStor wa).get k) := by
  have hinner : (Frame.ofCreate msg).inner = processCreateMessage.msg msg :=
    rfl
  have hsgEntry :
      (Frame.ofCreate msg).inner.benv.stat.rules.stateGas = Option.none := by
    rw [hinner, processCreateMessage.msg_benvStat]
    exact hsg
  have hCEntry : (Frame.ofCreate msg).inner.benv.state.getCode wa = C := by
    rw [hinner, processCreateMessage.msg_getCode]
    exact hC
  have hentryEntry :
      init = (((Frame.ofCreate msg).inner.benv.state.getStor wa).get k) := by
    rw [createEntry_getStor htargetNe]
    exact hentry
  exact trace.retained.cellProv_at trace.run k hsgEntry hCEntry hCne
    hsplit hentryEntry

/-- Settlement replay is cell provenance: the replayed cell is the entry
cell or a listed write's value. -/
theorem CellProv.of_replay_nodes {wa : Adr} {k init : B256}
    {nodes : List Exec.Deriv} {v : B256}
    {parent post : Devm} {writes : List Exec.StorageWrite}
    (hreplay : Exec.StorageReplay parent post writes)
    (hcode : (parent.getCode wa).toList ≠ [])
    (hinit : init = ((parent.getStor wa).get k))
    (hpost : v = ((post.getStor wa).get k))
    (mem : ∀ w ∈ writes, ∃ m ∈ nodes,
      Exec.Deriv.successfulSstore? m = some w) :
    CellProv wa k init nodes v := by
  have hcell := hreplay.2 wa hcode k
  rw [← hinit, ← hpost] at hcell
  exact CellProv.of_replayCell hcell.symm mem

/-- Every raw node of a retained call message carries its entry cell to the
message post: settlement replay (or entry preservation on rollback, inside
the replay transport) is cell provenance. -/
theorem ProcessMessageTrace.cellProv_post {msg : Msg} {post : Devm}
    (trace : ProcessMessageTrace msg (.ok post)) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = Option.none)
    {wa : Adr} {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) :
    CellProv wa k ((msg.benv.state.getStor wa).get k) trace.rawNodes
      ((post.getStor wa).get k) := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none =>
      have hprot : State.Protected msg.benv.state wa :=
        State.Protected.of_code_ne_nil (by rw [hC]; exact hCne)
      have hstor := ProcessMessage.none_ok_getStor_eq hrun wa hprot
      show CellProv wa k ((msg.benv.state.getStor wa).get k) []
        ((post.getStor wa).get k)
      exact Or.inl (congrArg (fun storage : Stor => storage.get k) hstor)
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hstat : sevm.benvStat = (Frame.ofCall msg).inner.benv.stat := by
        have e := Frame.enter_run_benvStat henter
        dsimp only at e
        exact e
      have hsg' : sevm.benvStat.rules.stateGas = Option.none := by
        rw [hstat]
        exact hsg
      have body : ∀ committed : Execution.commits execution = true,
          Exec.StorageReplay pre (Execution.committedPost execution
            committed) (Exec.retainedStorageWrites run) := by
        intro committed
        exact Exec.storageReplay_committedPost_noStateGas run committed
          hsg'
      let parent : Devm :=
        { pre with world := { pre.world with state := msg.benv.state } }
      have parentState : parent.state = msg.benv.state := rfl
      have hreplay : Exec.StorageReplay parent post
          (if Frame.settlementCommits (Frame.ofCall msg) execution = true
            then Exec.retainedStorageWrites run else []) :=
        ProcessMessage.storageReplay_of_body hrun parentState body
      have hcodeParent : (parent.getCode wa).toList ≠ [] := by
        have hparent : parent.getCode wa = msg.benv.state.getCode wa :=
          rfl
        rw [hparent, hC]
        exact hCne
      by_cases settles : Frame.settlementCommits (Frame.ofCall msg)
          execution = true
      · rw [ite_eq_left settles] at hreplay
        have mem : ∀ w ∈ Exec.retainedStorageWrites run, ∃ m ∈
            Exec.rawNodes run,
            Exec.Deriv.successfulSstore? m = some w := by
          intro w hw
          rw [Exec.retainedStorageWrites, List.mem_filterMap] at hw
          obtain ⟨m, hm, hfound⟩ := hw
          exact ⟨m,
            (Exec.retainedNodes_sublist_rawNodes run).subset hm, hfound⟩
        have hpost : ((post.getStor wa).get k) =
            ((post.getStor wa).get k) := rfl
        exact CellProv.of_replay_nodes hreplay hcodeParent rfl hpost mem
      · rw [ite_eq_right settles] at hreplay
        have mem : ∀ w ∈ ([] : List Exec.StorageWrite), ∃ m ∈
            Exec.rawNodes run,
            Exec.Deriv.successfulSstore? m = some w := by
          intro w hw
          simp only [List.not_mem_nil] at hw
        have hpost : ((post.getStor wa).get k) =
            ((post.getStor wa).get k) := rfl
        exact CellProv.of_replay_nodes hreplay hcodeParent rfl hpost mem

/-- A collision-free CREATE target holds no nonce and no code, hence is
unprotected. -/
theorem not_protected_target_of_noCollision {msg : Msg}
    (hcol : messageCreateCollision msg = false) :
    ¬ State.Protected msg.benv.state msg.currentTarget := by
  have hcol' : accountHasCodeOrNonce msg.benv.state msg.currentTarget =
      false := by
    simpa only [messageCreateCollision] using hcol
  unfold accountHasCodeOrNonce at hcol'
  rw [Bool.or_eq_false_iff] at hcol'
  intro hp
  unfold State.Protected at hp
  rcases hp with hn | hc
  · have hpos : msg.benv.state.getNonce msg.currentTarget > 0 :=
      UInt64.pos_iff_ne_zero.mpr hn
    exact (of_decide_eq_false hcol'.1) hpos
  · have hisempty :
        (msg.benv.state.getCode msg.currentTarget).isEmpty = true := by
      cases h : (msg.benv.state.getCode msg.currentTarget).isEmpty with
      | true => rfl
      | false =>
          simp only [h, Bool.not_false] at hcol'
          exact hcol'.2.symm
    have hsize : (msg.benv.state.getCode msg.currentTarget).size = 0 :=
      of_decide_eq_true hisempty
    exact hc (by simpa only [State.getCode] using hsize)

/-- A retained CREATE message carries its entry cell to the constructor
post: clean settlement replays the inner constructor body, other outcomes
restore the entry world, all inside the replay transport. -/
theorem ProcessCreateMessageTrace.cellProv_post {msg : Msg} {post : Devm}
    (trace : ProcessCreateMessageTrace msg (.ok post)) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = Option.none)
    {wa : Adr} {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ [])
    (hcol : messageCreateCollision msg = false) :
    CellProv wa k ((msg.benv.state.getStor wa).get k) trace.rawNodes
      ((post.getStor wa).get k) := by
  rcases trace with ⟨slot, retained, hrun⟩
  cases retained with
  | none =>
      have hprot : State.Protected msg.benv.state wa :=
        State.Protected.of_code_ne_nil (by rw [hC]; exact hCne)
      have htargetNe : msg.currentTarget ≠ wa :=
        ne_wa_of_not_hasCodeOrNonce (by rw [hC]; exact hCne)
          (by simpa only [messageCreateCollision] using hcol)
      have hstor :=
        ProcessCreateMessage.none_ok_getStor_eq_of_protected_ne hrun wa
          hprot htargetNe
      show CellProv wa k ((msg.benv.state.getStor wa).get k) []
        ((post.getStor wa).get k)
      exact Or.inl (congrArg (fun storage : Stor => storage.get k) hstor)
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hstat : sevm.benvStat = (Frame.ofCreate msg).inner.benv.stat := by
        have e := Frame.enter_run_benvStat henter
        dsimp only at e
        exact e
      have hsg' : sevm.benvStat.rules.stateGas = Option.none := by
        rw [hstat]
        have hinner :
            (Frame.ofCreate msg).inner = processCreateMessage.msg msg :=
          rfl
        rw [hinner, processCreateMessage.msg_benvStat]
        exact hsg
      have body : ∀ committed : Execution.commits execution = true,
          Exec.StorageReplay pre (Execution.committedPost execution
            committed) (Exec.retainedStorageWrites run) := by
        intro committed
        exact Exec.storageReplay_committedPost_noStateGas run committed
          hsg'
      let parent : Devm :=
        { pre with world := { pre.world with state := msg.benv.state } }
      have parentState : parent.state = msg.benv.state := rfl
      have hfresh : ¬ State.Protected parent.state msg.currentTarget := by
        rw [parentState]
        exact not_protected_target_of_noCollision hcol
      have hreplay : Exec.StorageReplay parent post
          (if Frame.settlementCommits (Frame.ofCreate msg) execution = true
            then Exec.retainedStorageWrites run else []) :=
        ProcessCreateMessage.storageReplay_of_body hrun parentState hfresh
          body
      have hcodeParent : (parent.getCode wa).toList ≠ [] := by
        have hparent : parent.getCode wa = msg.benv.state.getCode wa :=
          rfl
        rw [hparent, hC]
        exact hCne
      by_cases settles : Frame.settlementCommits (Frame.ofCreate msg)
          execution = true
      · rw [ite_eq_left settles] at hreplay
        have mem : ∀ w ∈ Exec.retainedStorageWrites run, ∃ m ∈
            Exec.rawNodes run,
            Exec.Deriv.successfulSstore? m = some w := by
          intro w hw
          rw [Exec.retainedStorageWrites, List.mem_filterMap] at hw
          obtain ⟨m, hm, hfound⟩ := hw
          exact ⟨m,
            (Exec.retainedNodes_sublist_rawNodes run).subset hm, hfound⟩
        have hpost : ((post.getStor wa).get k) =
            ((post.getStor wa).get k) := rfl
        exact CellProv.of_replay_nodes hreplay hcodeParent rfl hpost mem
      · rw [ite_eq_right settles] at hreplay
        have mem : ∀ w ∈ ([] : List Exec.StorageWrite), ∃ m ∈
            Exec.rawNodes run,
            Exec.Deriv.successfulSstore? m = some w := by
          intro w hw
          simp only [List.not_mem_nil] at hw
        have hpost : ((post.getStor wa).get k) =
            ((post.getStor wa).get k) := rfl
        exact CellProv.of_replay_nodes hreplay hcodeParent rfl hpost mem

/-- The EIP-7702 authorization prefix keeps a code-bearing owner's code,
from the entry code equation directly (no message invariant needed). -/
theorem delegation_keeps_code_entry {wa : Adr}
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ [])
    (hCdel : ¬ isValidDelegation C) :
    delegated.benv.state.getCode wa = C := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, -⟩
    exact hC
  · obtain ⟨⟨middle, counter⟩, hdel, rest⟩ := Except.bind_eq_ok run
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, -⟩
    have hkeep := (setDelegation_benv_equiv hdel).2 wa
      (by rw [hC]; exact hCne) (by rw [hC]; exact hCdel)
    exact hkeep.trans hC

/-- The resolved execution message holds the outer message's cell: code
delegation resolution and the authorization prefix keep storage. -/
theorem execMsg_cell_eq {wa : Adr}
    {msg delegated execMsg : Msg} {refund : Nat}
    (hexecMsg : execMsg = messageCallExecutionMessage delegated)
    (hdelegation : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    {C : ByteArray} (hC : msg.benv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (hCdel : ¬ isValidDelegation C) (k : B256) :
    ((execMsg.benv.state.getStor wa).get k) =
      ((msg.benv.state.getStor wa).get k) := by
  have hresolve :=
    ExecutionTrace.messageCallExecutionMessage_getStor delegated wa
  have hdeleg := messageCallDelegation_getStor_eq hdelegation wa
    (by rw [hC]; exact hCne) (by rw [hC]; exact hCdel)
  rw [← hexecMsg] at hresolve
  exact congrArg (fun storage : Stor => storage.get k)
    (hresolve.trans hdeleg)

/-- A settled message call inherits cell provenance from its own entry
world: the collision arm retains nothing, the create arm enters the
prepared inner message away from its target, the call arm enters the
resolved execution message. -/
theorem MessageCallTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = Option.none)
    (hC : msg.benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((msg.benv.state.getStor wa).get k)) :
    CellProv wa k init before ((n.devm.getStor wa).get k) := by
  cases trace with
  | createCollision htarget hcollision hresult =>
      simp only [MessageCallTrace.rawNodes] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  | createRun htarget hcollision evm hcore coreTrace hresult =>
      have htargetNe : msg.currentTarget ≠ wa :=
        ne_wa_of_not_hasCodeOrNonce (by rw [hC]; exact hCne)
          (by simpa only [messageCreateCollision] using hcollision)
      exact coreTrace.cellProv_at k hsg hC hCne htargetNe hsplit hentry
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm hcore
      coreTrace hresult =>
      have hsgExec : execMsg.benv.stat.rules.stateGas = Option.none := by
        rw [hexecMsg, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat hdelegation]
        exact hsg
      have hCExec : execMsg.benv.state.getCode wa = C := by
        rw [hexecMsg, messageCallExecutionMessage_getCode]
        exact delegation_keeps_code_entry hdelegation hC hCne hCdel
      have hentryExec :
          init = ((execMsg.benv.state.getStor wa).get k) := by
        rw [execMsg_cell_eq hexecMsg hdelegation hC hCne hCdel]
        exact hentry
      exact coreTrace.cellProv_at k hsgExec hCExec hCne hsplit hentryExec

/-- A settled message call carries its entry cell to its post cell: the
collision arm leaves the state, the run arms settle at their core state. -/
theorem MessageCallTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (k : B256)
    (hsg : msg.benv.stat.rules.stateGas = Option.none)
    (hC : msg.benv.state.getCode wa = C) (hCne : C.toList ≠ []) :
    CellProv wa k ((msg.benv.state.getStor wa).get k) trace.rawNodes
      ((state.getStor wa).get k) := by
  cases trace with
  | createCollision htarget hcollision hresult =>
      have hstate : state = msg.benv.state :=
        (processMessageCall_createCollision_out_noStateGas hsg htarget
          hcollision hresult).1
      show CellProv wa k ((msg.benv.state.getStor wa).get k) []
        ((state.getStor wa).get k)
      exact Or.inl (by rw [hstate])
  | createRun htarget hcollision evm hcore coreTrace hresult =>
      have hstate : state = evm.state :=
        (processMessageCall_createRun_out_noStateGas hsg htarget hcollision
          hcore hresult).1
      have htargetNe : msg.currentTarget ≠ wa :=
        ne_wa_of_not_hasCodeOrNonce (by rw [hC]; exact hCne)
          (by simpa only [messageCreateCollision] using hcollision)
      have hpost := coreTrace.cellProv_post k hsg hC hCne hcollision
      have hcell : ((state.getStor wa).get k) = ((evm.getStor wa).get k) := by
        rw [hstate]
        simp only [Devm.getStor, Devm.getAcct, State.getStor]
      show CellProv wa k ((msg.benv.state.getStor wa).get k)
        coreTrace.rawNodes ((state.getStor wa).get k)
      rw [hcell]
      exact hpost
  | callRun htarget delegated refund hdelegation execMsg hexecMsg evm hcore
      coreTrace hresult =>
      have hstate : state = evm.state :=
        (processMessageCall_callRun_out_noStateGas hsg htarget hdelegation
          hexecMsg hcore hresult).1
      have hsgExec : execMsg.benv.stat.rules.stateGas = Option.none := by
        rw [hexecMsg, messageCallExecutionMessage_benv_stat,
          messageCallDelegation_benv_stat hdelegation]
        exact hsg
      have hCExec : execMsg.benv.state.getCode wa = C := by
        rw [hexecMsg, messageCallExecutionMessage_getCode]
        exact delegation_keeps_code_entry hdelegation hC hCne hCdel
      have hpost := coreTrace.cellProv_post k hsgExec hCExec hCne
      have hcell : ((state.getStor wa).get k) = ((evm.getStor wa).get k) := by
        rw [hstate]
        simp only [Devm.getStor, Devm.getAcct, State.getStor]
      show CellProv wa k ((msg.benv.state.getStor wa).get k)
        coreTrace.rawNodes ((state.getStor wa).get k)
      rw [hcell, ← execMsg_cell_eq hexecMsg hdelegation hC hCne hCdel k]
      exact hpost

/-- A selected transaction inherits cell provenance from its own entry
world: the prepared message holds the entry cell across the nonce and
balance debit. -/
theorem TransactionTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((benv.state.getStor wa).get k)) :
    CellProv wa k init before ((n.devm.getStor wa).get k) := by
  have hbenv := prepareMessage_benv trace.prepared
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = Option.none := by
    rw [hbenv]
    exact hsg
  have hdebit : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode wa = C := by
    rw [hbenv]
    exact hdebit.trans hC
  have hmsgCell : ((trace.msg.benv.state.getStor wa).get k) =
      ((benv.state.getStor wa).get k) := by
    calc ((trace.msg.benv.state.getStor wa).get k)
        = ((trace.debitState.getStor wa).get k) := by rw [hbenv]
      _ = ((benv.state.getStor wa).get k) := congrArg
          (fun storage : Stor => storage.get k)
          (TransactionTrace.debitState_getStor_eq trace)
  have hmsgEntry : init = ((trace.msg.benv.state.getStor wa).get k) :=
    hentry.trans hmsgCell.symm
  exact trace.message.cellProv_at hCdel k hmsgSg hmsgState hCne hsplit
    hmsgEntry

/-- A transaction's top-level message runs its call target's own code. -/
theorem prepareMessage_own_entry {benv : Benv} {tenv : Tenv} {tx : Tx}
    {msg : Msg} (h : prepareMessage benv tenv tx = .ok msg) :
    msg.target.isNone = false →
      msg.codeAddress = some msg.currentTarget ∧
        msg.code = msg.benv.state.getCode msg.currentTarget := by
  intro htarget
  cases hr : tx.type.receiver? with
  | none =>
      unfold prepareMessage at h
      simp only [hr] at h
      obtain heq := Except.ok.inj h
      rw [← heq] at htarget
      simp only [Option.isNone_none, Bool.true_eq_false] at htarget
  | some target =>
      unfold prepareMessage at h
      simp only [hr] at h
      obtain heq := Except.ok.inj h
      rw [← heq]
      exact ⟨rfl, rfl⟩

/-- A selected transaction carries its entry cell to its post cell: the
message post settles through the gas credits, the deletion fold (which
never names the code-bearing owner), and the touched sweep. -/
theorem TransactionTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((benv.state.getStor wa).get k) trace.rawNodes
      ((state.getStor wa).get k) := by
  have hbenv := prepareMessage_benv trace.prepared
  have hmsgSg : trace.msg.benv.stat.rules.stateGas = Option.none := by
    rw [hbenv]
    exact hsg
  have hdebit : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode wa = C := by
    rw [hbenv]
    exact hdebit.trans hC
  have hnodel : Msg.NoDel wa trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using hnotCreated
    · rw [hmsgState]
      exact hCne
  have hown : trace.msg.target.isNone = false →
      trace.msg.codeAddress = some trace.msg.currentTarget ∧
        trace.msg.code =
          trace.msg.benv.state.getCode trace.msg.currentTarget :=
    prepareMessage_own_entry trace.prepared
  have hmsgNoDel := trace.message.noDel_of_safe hCdel hmsgSg hmsgState hown
    hnodel (trace.not_mem_msg_inheritedDeletions wa) safe
  obtain ⟨hnotDel, hmsgCode⟩ := hmsgNoDel
  have hnotList : ∀ x ∈ trace.messageOut.accountsToDelete.toList,
      x ≠ wa :=
    fun x hx heq => hnotDel (heq ▸ Std.HashSet.mem_toList.mp hx)
  obtain ⟨refundCounter, -, hfinal⟩ := trace.exists_selectedFinalStateForm hsg
  have hcodeAdd1 : (trace.messageState.getCode wa).toList ≠ [] := by
    rw [hmsgCode]
    exact hCne
  have hcodeAdd2 : ((trace.messageState.addBal trace.sender
      (((settleTransactionGas benv.stat.rules tx.gas
        trace.calldataFloorGasCost trace.messageOut.gasLeft
        trace.messageOut.stateGasLeft refundCounter
        trace.messageOut.stateGasUsed).gasLeft *
        trace.effectiveGasPrice).toB256)).getCode wa).toList ≠ [] := by
    rw [State.addBal_getCode, hmsgCode]
    exact hCne
  have hcodeSweep : (((trace.messageOut.accountsToDelete.toList.foldl
      destroyAccount ((trace.messageState.addBal trace.sender
        (((settleTransactionGas benv.stat.rules tx.gas
          trace.calldataFloorGasCost trace.messageOut.gasLeft
          trace.messageOut.stateGasLeft refundCounter
          trace.messageOut.stateGasUsed).gasLeft *
          trace.effectiveGasPrice).toB256)).addBal benv.stat.coinbase
        (((settleTransactionGas benv.stat.rules tx.gas
          trace.calldataFloorGasCost trace.messageOut.gasLeft
          trace.messageOut.stateGasLeft refundCounter
          trace.messageOut.stateGasUsed).gasUsed *
          (trace.effectiveGasPrice -
            benv.stat.baseFeePerGas)).toB256)))).getCode
      wa).toList ≠ [] := by
    rw [foldl_destroyAccount_getCode_ne _ hnotList, State.addBal_getCode,
      State.addBal_getCode, hmsgCode]
    exact hCne
  have hsettle : (state.getStor wa).get k =
      ((trace.messageState.getStor wa).get k) := by
    have hstateEq : state.getStor wa = trace.messageState.getStor wa := by
      have hcongr := congrArg (fun world : State => world.getStor wa) hfinal
      rw [sweepTouchedAccounts_getStor_of_nonempty _ _ hcodeSweep,
        foldl_destroyAccount_getStor hnotList,
        addBal_getStor_of_codenonempty hcodeAdd2,
        addBal_getStor_of_codenonempty hcodeAdd1] at hcongr
      exact hcongr
    exact congrArg (fun storage : Stor => storage.get k) hstateEq
  have hmsgCell : ((trace.msg.benv.state.getStor wa).get k) =
      ((benv.state.getStor wa).get k) := by
    calc ((trace.msg.benv.state.getStor wa).get k)
        = ((trace.debitState.getStor wa).get k) := by rw [hbenv]
      _ = ((benv.state.getStor wa).get k) := congrArg
          (fun storage : Stor => storage.get k)
          (TransactionTrace.debitState_getStor_eq trace)
  have msgPost := trace.message.cellProv_post hCdel k hmsgSg hmsgState hCne
  have entryBridge : CellProv wa k ((benv.state.getStor wa).get k) []
      ((trace.msg.benv.state.getStor wa).get k) :=
    Or.inl hmsgCell
  have settleBridge : CellProv wa k
      ((trace.messageState.getStor wa).get k) []
      ((state.getStor wa).get k) :=
    Or.inl hsettle
  have e12 := CellProv.trans entryBridge msgPost
  rw [List.nil_append] at e12
  have e123 := CellProv.trans e12 settleBridge
  rw [List.append_nil] at e123
  exact e123

end ExecutionTrace

end Blanc
