import Blanc.Lift.UniswapV2Pair.PermitEntries
import Blanc.Lift.UniswapV2Pair.ApproveSource
import Blanc.Lift.CalldataGuards
import Blanc.Lift.Ecrecover

/-! The literal permit bytecode refines the typed permit segment and its recovery resume. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def permitDecodedEntry (sevm : Sevm) : Entry :=
  .permit (permitOwner sevm) (permitSpender sevm) (permitValue sevm) (permitDeadline sevm)
    (permitV sevm) (permitR sevm) (permitS sevm)

def permitTouched (owner spender : Adr) : List WriterKey := [.nonce owner, .allowance owner spender]

def nonceSourceState (st : State) (owner : Adr) (value : B256) : State :=
  { st with nonces := Function.update st.nonces owner value }

/-- Wrapped postincrement of the old nonce, then the approval. -/
def permitSourceState (st : State) (owner spender : Adr) (value : B256) : State :=
  approveSourceState (nonceSourceState st owner (st.nonces owner + 1)) owner spender value

def permitRequest (st : State) (owner spender : Adr) (value deadline : B256) (v : UInt8)
    (r s : B256) : Request :=
  requestFor .permitRecovery 1
    (.recover (permitDigest st owner spender value (st.nonces owner) deadline) v r s)

def permitSuspendedFrame (current : Checkpoint) (ctx : Context) (owner spender : Adr)
    (value deadline : B256) (v : UInt8) (r s : B256) : Frame :=
  (Frame.enter current ctx (.permit owner spender value deadline v r s)).withEvents
    (nonceSourceState current.state owner (current.state.nonces owner + 1)) []

/-- The observed reply: success, the full return bytes, and the copied word as recovery output.
The code bit is immaterial because the recovery request does not require code. -/
def permitExternalResult (out : Bytes) (codeExists : Bool) : ExternalResult :=
  { success := true, returndata := out, codeExists := codeExists,
    recoveryOutput := permitRecoveredWord out }

def permitSourceFrame (current : Checkpoint) (ctx : Context) (owner spender : Adr)
    (value deadline : B256) (v : UInt8) (r s : B256) : Frame :=
  ((permitSuspendedFrame current ctx owner spender value deadline v r s).beginResume
    (permitRequest current.state owner spender value deadline v r s)).withEvents
    (permitSourceState current.state owner spender value) [.approval owner spender value]

def permitSourceDone (current : Checkpoint) (ctx : Context) (owner spender : Adr)
    (value deadline : B256) (v : UInt8) (r s : B256) : RunResult :=
  { status := .success [], frame := permitSourceFrame current ctx owner spender value deadline v r s,
    remaining := .done, childReturns := [] }

theorem permit_startTyped_suspended {current : Checkpoint} {ctx : Context} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256}
    (paid : ctx.value = 0) (timely : ctx.timestamp ≤ deadline) (nonstatic : ctx.isStatic = false) :
    startTyped current ctx (.permit owner spender value deadline v r s) =
      .suspended (permitSuspendedFrame current ctx owner spender value deadline v r s)
        (permitRequest current.state owner spender value deadline v r s)
        (.permitRecovery owner spender value) := by
  have immediate : startImmediate current ctx (.permit owner spender value deadline v r s) = none := by
    simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad paid), getterResult]
  simp only [startTyped, immediate, timely, ite_true, nonstatic, Bool.false_eq_true, ite_false]
  rfl

theorem permit_resume_finished {current : Checkpoint} {ctx : Context} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256} {out : Bytes} {codeExists : Bool}
    (nonstatic : ctx.isStatic = false) (recovered : (permitRecoveredWord out).toAdr ≠ 0)
    (signer : (permitRecoveredWord out).toAdr = owner) :
    resumeSegment (permitSuspendedFrame current ctx owner spender value deadline v r s)
      (permitRequest current.state owner spender value deadline v r s)
      (.permitRecovery owner spender value) (permitExternalResult out codeExists) =
      .finished (permitSourceFrame current ctx owner spender value deadline v r s) [] := by
  have decoded : decodeExternal (permitRequest current.state owner spender value deadline v r s)
      (permitExternalResult out codeExists) = .ok (.address (permitRecoveredWord out).toAdr) := rfl
  have accepted : ((permitRecoveredWord out).toAdr ≠ 0 ∧ (permitRecoveredWord out).toAdr = owner) =
      True := eq_true ⟨recovered, signer⟩
  simp only [resumeSegment, decoded, accepted, ite_true]
  have context : ((permitSuspendedFrame current ctx owner spender value deadline v r s).beginResume
      (permitRequest current.state owner spender value deadline v r s)).context = ctx := rfl
  rw [context, approveLP_accept nonstatic]
  rfl

theorem permit_exact_consumes {current : Checkpoint} {ctx : Context} {owner spender : Adr}
    {value deadline : B256} {v : UInt8} {r s : B256} {out : Bytes} {codeExists : Bool}
    (paid : ctx.value = 0) (timely : ctx.timestamp ≤ deadline) (nonstatic : ctx.isStatic = false)
    (recovered : (permitRecoveredWord out).toAdr ≠ 0)
    (signer : (permitRecoveredWord out).toAdr = owner) :
    ExactConsumes (startTyped current ctx (.permit owner spender value deadline v r s))
      (.next (permitExternalResult out codeExists) .done .done)
      (permitSourceDone current ctx owner spender value deadline v r s) := by
  rw [permit_startTyped_suspended paid timely nonstatic]
  have rest := permit_resume_finished (current := current) (deadline := deadline) (v := v)
    (r := r) (s := s) (value := value) (spender := spender) (codeExists := codeExists)
    nonstatic recovered signer
  have consumed := ExactConsumes.nextCall
    (frame := permitSuspendedFrame current ctx owner spender value deadline v r s)
    (request := permitRequest current.state owner spender value deadline v r s)
    (continuation := .permitRecovery owner spender value)
    (result := permitExternalResult out codeExists) (turns := .done) (tail := .done)
    (out := permitSourceDone current ctx owner spender value deadline v r s) rfl (fun _ => rfl)
    (ExactTurns.done _ _ 0) (by
      change ExactConsumes (resumeSegment (permitSuspendedFrame current ctx owner spender value
        deadline v r s) (permitRequest current.state owner spender value deadline v r s)
        (.permitRecovery owner spender value) (permitExternalResult out codeExists)) .done _
      rw [rest]
      exact ExactConsumes.finished _ [])
  exact consumed

theorem nonceSourceState_value (st : State) (owner : Adr) (value : B256) (k : WriterKey) :
    k.value (nonceSourceState st owner value) =
      if k = .nonce owner then value else k.value st := by
  cases k with
  | allowance a p => rfl
  | balance a => rfl
  | nonce a =>
    dsimp only [WriterKey.value, nonceSourceState]
    by_cases same : a = owner
    · subst a
      rw [Function.update_self, ite_eq_left rfl]
    · have different : WriterKey.nonce a ≠ .nonce owner :=
        fun eq => same (WriterKey.nonce.inj eq)
      rw [Function.update_of_ne same, ite_eq_right different]

/-- A tracked nonce store preserves the fixed rows and every other logical map. -/
theorem WriterRep.nonce_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {owner : Adr} {value : B256} (rep : WriterRep K s st) (tracked : K (.nonce owner)) :
    WriterRep K (s.set (WriterKey.slot (.nonce owner)) value) (nonceSourceState st owner value) := by
  have off := rep.apart (.nonce owner) tracked
  have unchanged (n : B256) (fixed : n ∈ writerFixedSlots) :
      (s.set (WriterKey.slot (.nonce owner)) value).get n = s.get n :=
    Stor.get_set_ne s (k := WriterKey.slot (.nonce owner)) (a := n)
      (fun eq => off (eq.symm ▸ fixed)) value
  refine ⟨rep.finite, ?_, rep.support.set tracked value, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches, nonceSourceState]
    rw [unchanged 0 (by decide), unchanged 3 (by decide), unchanged 5 (by decide),
      unchanged 6 (by decide), unchanged 7 (by decide), unchanged 8 (by decide),
      unchanged 9 (by decide), unchanged 10 (by decide), unchanged 11 (by decide),
      unchanged 12 (by decide)]
    exact rep.fixed
  · intro k member
    by_cases same : k = .nonce owner
    · subst k
      rw [Stor.get_set_self, nonceSourceState_value, ite_eq_left rfl]
    · have separate : WriterKey.slot (.nonce owner) ≠ k.slot :=
        fun eq => same (rep.inj k (.nonce owner) member tracked eq.symm)
      rw [Stor.get_set_ne s separate value, nonceSourceState_value, ite_eq_right same]
      exact rep.selected k member
  · intro k outside
    have different : k ≠ .nonce owner := by
      intro eq
      subst k
      exact outside tracked
    rw [nonceSourceState_value, ite_eq_right different]
    exact rep.logicalZero k outside

/-- Sequential nonce then allowance stores over the one extended trace-local footprint. -/
theorem WriterRep.permit_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {owner spender : Adr} {value : B256} (rep : WriterRep K s st)
    (fresh : WriterFreshKeys K (permitTouched owner spender)) :
    WriterRep (WriterExtend K (permitTouched owner spender))
      ((s.set (permitNonceSlot owner) (st.nonces owner + 1)).set
        (mapSlot spender.toB256 (mapSlot owner.toB256 2)) value)
      (permitSourceState st owner spender value) := by
  have extended := rep.extend fresh
  have nonceKey : WriterExtend K (permitTouched owner spender) (.nonce owner) :=
    .inr (List.mem_cons.mpr (.inl rfl))
  have stored := extended.nonce_store (value := st.nonces owner + 1) nonceKey
  have touched : ∀ k ∈ approveTouched owner spender,
      WriterExtend K (permitTouched owner spender) k := by
    intro k hk
    simp only [approveTouched, List.mem_singleton] at hk
    subst k
    exact .inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))
  have selectedFresh : WriterFreshKeys (WriterExtend K (permitTouched owner spender))
      (approveTouched owner spender) :=
    Blanc.SlotFootprint.FreshKeys.of_universe stored.inj stored.apart (fun _ h => h) touched
  have approved := stored.approve_store (amount := value) selectedFresh
  have keys : WriterExtend (WriterExtend K (permitTouched owner spender))
      (approveTouched owner spender) = WriterExtend K (permitTouched owner spender) := by
    funext k
    apply propext
    constructor
    · rintro (old | new)
      · exact old
      · exact touched k new
    · intro old
      exact .inl old
  rw [keys] at approved
  exact approved

/-- The raw old-nonce and domain reads are the tracked logical values. -/
theorem permit_reads {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    {owner spender : Adr}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (permitTouched owner spender)) :
    permitNonceRead sevm b owner = st.nonces owner ∧
      b.getStorVal sevm.currentTarget 3 = st.domainSeparator := by
  have extended := rep.extend fresh
  have member : WriterExtend K (permitTouched owner spender) (.nonce owner) :=
    .inr (List.mem_cons.mpr (.inl rfl))
  refine ⟨?_, rep.fixed.2.1⟩
  have read := extended.selected (.nonce owner) member
  unfold permitNonceRead
  change ((afterSload sevm b 3).getStor sevm.currentTarget).get (permitNonceSlot owner) = _
  rw [afterSload_getStor]
  exact read

theorem permitCallDigest_source {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    {owner spender : Adr} {value deadline : B256}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (permitTouched owner spender)) :
    permitCallDigest sevm b owner spender value deadline =
      permitDigest st owner spender value (st.nonces owner) deadline := by
  obtain ⟨nonce, domain⟩ := permit_reads (spender := spender) rep fresh
  unfold permitCallDigest permitDigestOf permitInner permitDigest
  rw [nonce, domain]

/-- Raw post facts over the actual call world: the call preserves storage, logs and output. -/
theorem permitPublicPost_facts {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {out : Bytes}
    {sel : B256} {G : Nat}
    (post : StaticCallPost (permitNonceWorld sevm b (permitOwner sevm)) d S M 482 128 450 32 1 out) :
    (permitPublicPost sevm b d out sel G).output = b.output ∧
    (permitPublicPost sevm b d out sel G).logs = b.logs ++
      [approvalRawLog sevm.currentTarget (permitOwner sevm) (permitSpender sevm) (permitValue sevm)] ∧
    (permitPublicPost sevm b d out sel G).getStor sevm.currentTarget =
      (((b.getStor sevm.currentTarget).set (permitNonceSlot (permitOwner sevm))
        (permitNonceRead sevm b (permitOwner sevm) + 1)).set
        (mapSlot (permitSpender sevm).toB256 (mapSlot (permitOwner sevm).toB256 2))
        (permitValue sevm)) ∧
    (∀ a, a ≠ sevm.currentTarget →
      (permitPublicPost sevm b d out sel G).getStor a = b.getStor a) ∧
    (permitPublicPost sevm b d out sel G).gasLeft = G := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · change (afterSstore sevm d (mapSlot (permitSpender sevm).toB256 (mapSlot (permitOwner sevm).toB256 2))
      (permitValue sevm)).output = _
    rw [afterSstore_output, post.output rfl]
    unfold permitNonceWorld
    rw [afterSstore_output, afterSload_output, afterSload_output]
  · change (afterSstore sevm d (mapSlot (permitSpender sevm).toB256 (mapSlot (permitOwner sevm).toB256 2))
      (permitValue sevm)).logs ++
      [approvalRawLog sevm.currentTarget (permitOwner sevm) (permitSpender sevm) (permitValue sevm)] = _
    rw [afterSstore_logs, post.logs]
    unfold permitNonceWorld
    rw [afterSstore_logs, afterSload_logs, afterSload_logs]
  · change Devm.getStor (approveCoreBase sevm d (permitOwner sevm) (permitSpender sevm) (permitValue sevm))
      sevm.currentTarget = _
    rw [approveCoreBase, Devm.addLog_getStor, afterSstore_getStor_self, post.stor]
    unfold permitNonceWorld
    rw [afterSstore_getStor_self, afterSload_getStor, afterSload_getStor]
  · intro a different
    change Devm.getStor (approveCoreBase sevm d (permitOwner sevm) (permitSpender sevm) (permitValue sevm)) a = _
    rw [approveCoreBase, Devm.addLog_getStor, afterSstore_getStor_ne _ _ _ _ _ different.symm,
      post.stor]
    unfold permitNonceWorld
    rw [afterSstore_getStor_ne _ _ _ _ _ different.symm, afterSload_getStor, afterSload_getStor]

def permitSourceOrigin (ctx : Context) : ReceiptOrigin :=
  { invocation := ctx.invocation, segment := 1, afterCall := some .permitRecovery }

/-- Local frame facts of one successful permit frame at its observed recovery reply. -/
def PermitSourceResult (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat)
    (sevm : Sevm) (b post d : Devm) (out : Bytes) (codeExists : Bool) (residual : Nat) : Prop :=
  post = permitPublicPost sevm b d out 0xd505accf residual ∧
  WriterRep (WriterExtend K (permitTouched (permitOwner sevm) (permitSpender sevm)))
    (post.getStor sevm.currentTarget)
    (permitSourceState current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)) ∧
  startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm) =
    .suspended (permitSuspendedFrame current (writerContext sevm invocation) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm)
      (permitS sevm))
      (permitRequest current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
        (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm))
      (.permitRecovery (permitOwner sevm) (permitSpender sevm) (permitValue sevm)) ∧
  (permitRequest current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
    (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).calldata =
    ExternalOperation.encode
      (.recover (permitPublicDigest sevm b) (permitV sevm) (permitR sevm) (permitS sevm)) ∧
  (permitRequest current.state (permitOwner sevm) (permitSpender sevm) (permitValue sevm)
    (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).target = (1 : B256).toAdr ∧
  ExactConsumes (startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm))
    (.next (permitExternalResult out codeExists) .done .done)
    (permitSourceDone current (writerContext sevm invocation) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm)
      (permitS sevm)) ∧
  drive 3 (startTyped current (writerContext sevm invocation) (permitDecodedEntry sevm))
    (.next (permitExternalResult out codeExists) .done .done) =
    permitSourceDone current (writerContext sevm invocation) (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm)
      (permitS sevm) ∧
  (permitSourceFrame current (writerContext sevm invocation) (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).checkpoint =
    current ∧
  (permitSourceFrame current (writerContext sevm invocation) (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).current.logs =
    current.logs ++ [.owned (permitSourceOrigin (writerContext sevm invocation))
      (.approval (permitOwner sevm) (permitSpender sevm) (permitValue sevm))] ∧
  (permitSourceFrame current (writerContext sevm invocation) (permitOwner sevm) (permitSpender sevm)
    (permitValue sevm) (permitDeadline sevm) (permitV sevm) (permitR sevm) (permitS sevm)).current.updates =
    current.updates ∧
  post.output = [] ∧
  post.logs = b.logs ++
    [approvalRawLog sevm.currentTarget (permitOwner sevm) (permitSpender sevm) (permitValue sevm)] ∧
  post.getStor sevm.currentTarget =
    (((b.getStor sevm.currentTarget).set (permitNonceSlot (permitOwner sevm))
      (current.state.nonces (permitOwner sevm) + 1)).set
      (mapSlot (permitSpender sevm).toB256 (mapSlot (permitOwner sevm).toB256 2))
      (permitValue sevm)) ∧
  (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) ∧
  post.gasLeft = residual

/-- The result from the raw guards: the typed segment, its resume, and the exact post. -/
theorem permit_public_source_result {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {out : Bytes}
    {codeExists : Bool} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (permitTouched (permitOwner sevm) (permitSpender sevm)))
    (freshOutput : b.output = [])
    (paid : sevm.value = 0) (nonstatic : sevm.isStatic = false)
    (timely : sevm.benvStat.time ≤ permitDeadline sevm)
    (post : StaticCallPost (permitNonceWorld sevm b (permitOwner sevm)) d S M 482 128 450 32 1 out)
    (recovered : (permitRecoveredWord out).toAdr ≠ 0)
    (signer : (permitRecoveredWord out).toAdr = permitOwner sevm) :
    PermitSourceResult K current invocation sevm b (permitPublicPost sevm b d out 0xd505accf G)
      d out codeExists G := by
  obtain ⟨output, logs, storage, foreign, gas⟩ := permitPublicPost_facts (sel := 0xd505accf)
    (G := G) post
  obtain ⟨nonce, _⟩ := permit_reads (spender := permitSpender sevm) rep fresh
  have digest := permitCallDigest_source (value := permitValue sevm)
    (deadline := permitDeadline sevm) rep fresh
  have consumed := permit_exact_consumes (current := current) (ctx := writerContext sevm invocation)
    (codeExists := codeExists) (owner := permitOwner sevm) (spender := permitSpender sevm)
    (value := permitValue sevm) (deadline := permitDeadline sevm) (v := permitV sevm) (r := permitR sevm) (s := permitS sevm)
    paid timely nonstatic recovered signer
  rw [nonce] at storage
  refine ⟨rfl, ?_, permit_startTyped_suspended paid timely nonstatic, ?_, rfl, consumed,
    ExactConsumes.realizes consumed 3 (by show 1 + 0 + 0 + 1 ≤ 3; omega), rfl, ?_, rfl,
    output.trans freshOutput, logs, storage, foreign, gas⟩
  · rw [storage]
    exact rep.permit_store fresh
  · change ExternalOperation.encode (.recover (permitDigest current.state (permitOwner sevm)
      (permitSpender sevm) (permitValue sevm) (current.state.nonces (permitOwner sevm))
      (permitDeadline sevm)) (permitV sevm) (permitR sevm) (permitS sevm)) = _
    rw [← digest]
    rfl
  · change (current.logs ++ List.map _ []) ++ List.map _ [_] = _
    rw [List.map_nil, List.append_nil]
    rfl

/-- Every successful literal permit run derives value zero, at least 228 calldata bytes,
nonstatic, timely, a successful recovery call whose copied word is the nonzero owner, and the
typed segment with its resume at that observed reply. No source endpoint is a premise; the
observation is an input, never a claim that signatures are unforgeable. -/
theorem permit_bytecode_refines_source {K : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : WriterFreshKeys K (permitTouched (permitOwner sevm) (permitSpender sevm)))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd505accf) (freshOutput : b.output = [])
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ 228 ≤ sevm.data.length ∧ sevm.isStatic = false ∧
      sevm.benvStat.time ≤ permitDeadline sevm ∧
      ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (residual : Nat),
        PermitRawCall sevm b 0xd505accf gw callGas d out ∧
        ∀ codeExists, PermitSourceResult K current invocation sevm b post d out codeExists residual := by
  obtain ⟨paid, size, guard, nonstatic, timely, gw, callGas, d, out, residual, call, eq⟩ :=
    permit_bytecode_refines_raw codeEq fork selector run
  have length := (word_calldata_guards_iff (n := 224) representable (by decide)).mp ⟨size, guard⟩
  refine ⟨paid, length, nonstatic, timely, gw, callGas, d, out, residual, call, fun codeExists => ?_⟩
  rw [eq]
  exact permit_public_source_result rep fresh freshOutput paid nonstatic timely call.2.1
    call.2.2.2.2.1 call.2.2.2.2.2

end Blanc.Lift.UniswapV2Pair
