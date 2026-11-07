import Blanc.Lift.RequestSystem.Effects
import Blanc.Lift.BuilderRequest.Deposit.Fifo
import Blanc.Lift.BuilderRequest.Exit.Fifo
import Blanc.Lift.BuilderRequest.Deposit.SubmissionAmsterdam
import Blanc.Lift.BuilderRequest.Exit.SubmissionAmsterdam

/-!
# The builders' system caller, outside the request phase, and their output length

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

The contracts' dispatch asks only whether `CALLER` is `SYSTEM_ADDRESS`. It cannot see whether the frame is the
request phase's. `system_caller_frame` compiles the consequence: a frame with caller SYSTEM, in any context,
drains the queue and returns the records to its caller, and the request phase's later call at that post state
returns only what is left. So "nothing dropped" needs a premise: **no frame outside the request phase has
caller SYSTEM**. For any other caller, the frame law excludes the drain (`non_system_keeps_head`).

What is and isn't compiled. The frame is compiled at frame level: `Exec` from a `Ready` base, whose reservoir
holds the four stores' state gas. `foreign_witness` meets the premises at a message that is not the system
message (another origin, depth 0, a reservoir of the system grant's size). Not compiled: such a message arising
from a transaction or a `CALL`, so no message-level return to a caller and no rollback or settlement; a frame on
an empty reservoir, where state gas spills into `gasLeft`; and whether anything can send as `SYSTEM_ADDRESS` on
mainnet at all, which no theorem here addresses: that is a question for reads of the actual state.

`output_length` is separate: each builder's system call returns a whole number of records, at most the cap,
from any storage.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestSystem

/-- A builder's system call, read on a queue. -/
structure QueueCall (k : SysPath) (Record : Type) where
  call : SysCall k
  output : SysOutput k call.memory
  /-- Slots per record. -/
  width : Nat
  words : Record → Nat → B256
  out : Record → Bytes
  next_eq : k.shape.next = excessNext k.shape.target.word
  /-- A record's returned bytes are never empty. -/
  out_ne : ∀ r, out r ≠ []
  /-- The output half of the contract's FIFO. -/
  fifo : ∀ {benv : Benv} {st : QueueState Record}, benv.stat.fork = .amsterdam →
    benv.state.getCode call.target = k.code →
    Represents width words (storOf benv.state call.target) st →
    (SysPath.callPost k benv call.target).output = (st.queue.take k.capN).flatMap out

/-- A drain leaves the queue less its oldest `cap` records, whatever its length. -/
theorem drainedState_queue {Record : Type} (cap : Nat) (target : B256) (st : QueueState Record) :
    (drainedState cap target st).queue = st.queue.drop cap := by
  unfold drainedState
  dsimp only
  split
  · rename_i h
    exact (List.drop_eq_nil_of_le h).symm
  · rfl

namespace QueueCall

variable {k : SysPath} {Record : Type} (q : QueueCall k Record)

/-- The call's exact result, and what it returns on a queue. -/
theorem call_queue {benv : Benv} {st : QueueState Record} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode q.call.target = k.code)
    (rep : Represents q.width q.words (storOf benv.state q.call.target) st) :
    ∃ out, processCheckedSystemTransaction benv q.call.target [] =
        .ok (sysState k.shape benv.state q.call.target, out) ∧
      out.returnData = (st.queue.take k.capN).flatMap q.out :=
  ⟨_, (q.call.spec hfork installed).1, q.fifo hfork installed rep⟩

/-- **A frame with caller SYSTEM, in any context, drains the queue past the request phase.** Under Amsterdam, on
storage representing a queue, a non-static empty-calldata frame at the contract's code whose caller is SYSTEM
succeeds. It returns the oldest `min(length, cap)` records to that caller and leaves the queue without them. The
request phase's call at that post state, at any Amsterdam environment, then returns the next records only. The
frame's message need not be the system message: `Sevm` and base are arbitrary, under `Ready` and the gas premise.
Frame level only: this is not a statement that a chain produces such a frame. -/
theorem system_caller_frame {sevm : Sevm} {b : Devm} {G : Nat} {st : QueueState Record} {benv : Benv}
    (hcode : sevm.code = k.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (hstatic : sevm.isStatic = false) (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (htarget : sevm.currentTarget = q.call.target) (r : Ready sevm b [2, 3, 0, 1])
    (hG : gCallStipend < G) (hb : benv.stat.fork = .amsterdam)
    (installed : b.state.getCode q.call.target = k.code)
    (rep : Represents q.width q.words (storOf b.state q.call.target) st) :
    ∃ post : Devm, Nonempty (Exec 0 sevm (St b [] .empty (G + k.frameCost sevm b)) (.ok post)) ∧
      post.output = (st.queue.take k.capN).flatMap q.out ∧
      post.state = sysState k.shape b.state q.call.target ∧
      Represents q.width q.words (storOf post.state q.call.target) (drainedState k.capN k.shape.target.word st) ∧
      ∃ out, processCheckedSystemTransaction (benv.withState post.state) q.call.target [] =
          .ok (sysState k.shape post.state q.call.target, out) ∧
        out.returnData = ((st.queue.drop k.capN).take k.capN).flatMap q.out := by
  have hstate : (k.framePost sevm b G).state = sysState k.shape b.state q.call.target := by
    rw [SysPath.framePost_state, htarget]
  have hrep : Represents q.width q.words (storOf (k.framePost sevm b G).state q.call.target) (drainedState k.capN k.shape.target.word st) := by
    rw [hstate]
    exact represents_sysState k.shape k.cap_word q.next_eq rep
  have hoff : (k.framePost sevm b G).state.getCode q.call.target = k.code := by
    rw [hstate, sysState_getCode]
    exact installed
  obtain ⟨out, hc, hr⟩ := q.call_queue (benv := benv.withState (k.framePost sevm b G).state) hb hoff hrep
  refine ⟨_, k.frame_exec hcode hfork hstatic hcaller hdata r hG, ?_, hstate, hrep, out, hc, ?_⟩
  · rw [q.output.framePost_output_eq_callPost sevm b G (benv.withState b.state) rfl htarget]
    exact q.fifo hb installed rep
  · rw [hr, drainedState_queue]

/-- **Without the premise, "nothing dropped" fails.** On a non-empty queue that fits one call, a SYSTEM-caller
frame outside the request phase returns every record, non-empty, to its caller. The request phase's call at the
post state then returns nothing, so its step of `runRequestContracts` adds no entry and the incoming list is
unchanged, while the same call at the pre state would have returned exactly those bytes. No later call recovers
them: the post storage represents the empty queue. -/
theorem records_miss_requests {sevm : Sevm} {b : Devm} {G : Nat} {st : QueueState Record} {benv : Benv}
    (hcode : sevm.code = k.code) (hfork : sevm.benvStat.fork = .amsterdam)
    (hstatic : sevm.isStatic = false) (hcaller : sevm.caller = systemAddress) (hdata : sevm.data = [])
    (htarget : sevm.currentTarget = q.call.target) (r : Ready sevm b [2, 3, 0, 1])
    (hG : gCallStipend < G) (hb : benv.stat.fork = .amsterdam)
    (installed : b.state.getCode q.call.target = k.code)
    (rep : Represents q.width q.words (storOf b.state q.call.target) st)
    (hne : st.queue ≠ []) (fits : st.queue.length ≤ k.capN)
    (idx : Nat) (ty : UInt8) (rest : List (UInt8 × Adr)) (acc : List Bytes) (bal : BalBuilder) :
    ∃ post : Devm, Nonempty (Exec 0 sevm (St b [] .empty (G + k.frameCost sevm b)) (.ok post)) ∧
      post.output = st.queue.flatMap q.out ∧ post.output ≠ [] ∧
      (drainedState k.capN k.shape.target.word st).queue = [] ∧
      Represents q.width q.words (storOf post.state q.call.target) (drainedState k.capN k.shape.target.word st) ∧
      (∃ out, processCheckedSystemTransaction (benv.withState b.state) q.call.target [] =
          .ok (sysState k.shape b.state q.call.target, out) ∧ out.returnData = post.output) ∧
      ∃ bal', runRequestContracts idx ((ty, q.call.target) :: rest) (benv.withState post.state) acc bal =
        runRequestContracts idx rest
          ((benv.withState post.state).withState (sysState k.shape post.state q.call.target)) acc bal' := by
  obtain ⟨post, hexec, hout, hstate, hrep, out, hc, hr⟩ :=
    q.system_caller_frame (benv := benv) hcode hfork hstatic hcaller hdata htarget r hG hb installed rep
  have hdrop : st.queue.drop k.capN = [] := List.drop_eq_nil_of_le fits
  have htake : st.queue.take k.capN = st.queue := List.take_of_length_le fits
  have hempty : out.returnData = [] := by
    rw [hr, hdrop, List.take_nil, List.flatMap_nil]
  have hout' : post.output = st.queue.flatMap q.out := by rw [hout, htake]
  have hstep := runRequestContracts_step (idx := idx) (ty := ty) (rest := rest) (acc := acc) (bal := bal) hc
  obtain ⟨o2, hc2, hr2⟩ := q.call_queue (benv := benv.withState b.state) hb installed rep
  refine ⟨post, hexec, hout', ?_, (by rw [drainedState_queue, hdrop]), hrep, ⟨o2, hc2, by rw [hr2, hout]⟩, ?_⟩
  · rw [hout']
    intro empty
    obtain ⟨x, xs, hq⟩ := List.exists_cons_of_ne_nil hne
    rw [hq, List.flatMap_cons] at empty
    exact q.out_ne x (List.append_eq_nil_iff.mp empty).1
  · rw [hstep, hempty]
    exact ⟨_, rfl⟩

end QueueCall

/-! ## Output length -/

/-- Each call's return length, from the call's own result. -/
theorem call_output_length {k : SysPath} (c : SysCall k) (o : SysOutput k c.memory) {benv : Benv}
    (hfork : benv.stat.fork = .amsterdam) (installed : benv.state.getCode c.target = k.code) :
    ∃ post out, processCheckedSystemTransaction benv c.target [] = .ok (post, out) ∧
      out.returnData.length = c.memory.lenN *
        (drainCount k.shape.cap.word ((benv.state.getStor c.target).get 2)
          ((benv.state.getStor c.target).get 3)).toNat ∧
      (drainCount k.shape.cap.word ((benv.state.getStor c.target).get 2)
        ((benv.state.getStor c.target).get 3)).toNat ≤ k.capN :=
  ⟨_, _, (c.spec hfork installed).1, o.callPost_output_length benv c.target⟩

/-! ## A frame outside the request phase -/

/-- An Amsterdam environment exists, so the fork premise here can be met. -/
theorem amsterdam_benv_exists : ∃ benv : Benv, benv.stat.fork = .amsterdam :=
  ⟨{ (default : Benv) with stat := { (default : Benv).stat with fork := .amsterdam } }, rfl⟩

section Witness

variable (benv : Benv) (target : Adr) (code : ByteArray)

/-- A message with caller SYSTEM that is not the system message: its origin is `origin` and its depth 0. -/
def foreignMsg (origin : Adr) : Msg :=
  let m := systemCallMsg benv target code []
  { m with depth := 0, tenv := { m.tenv with stat := { m.tenv.stat with origin := origin } } }

variable {benv target code} {origin : Adr}

theorem foreign_St :
    St (initDevm (foreignMsg benv target code origin)) [] .empty systemTransactionGas =
      initDevm (foreignMsg benv target code origin) := rfl

/-- The foreign message's base is ready for the frame's four stores, from a reservoir of the system grant's
size. -/
theorem foreign_ready (hfork : benv.stat.fork = .amsterdam) :
    Ready (initSevm (foreignMsg benv target code origin)) (initDevm (foreignMsg benv target code origin))
      [2, 3, 0, 1] where
  error := rfl
  refund := Int.le_refl 0
  spill := rfl
  reservoir := by
    have hs : (benv.beginTransaction).stat.rules.stateGas = some amsterdamStateGasRules :=
      amsterdam_stateGas hfork
    show _ ≤ (match (benv.beginTransaction).stat.rules.stateGas with
      | none => 0
      | some state => state.systemReservoir)
    rw [hs]
    decide
  clean := fun k' _ => by
    unfold SlotClean Devm.getOrigStorVal
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

end Witness

namespace QueueCall

variable {k : SysPath} {Record : Type} (q : QueueCall k Record)

/-- **The premises can be met, by a frame that is not the system message.** Under Amsterdam, on any state holding
the code and a non-empty queue that fits one call, the message from `foreignMsg`, whose origin is not SYSTEM and
whose depth is not the system message's 1024, satisfies `records_miss_requests`. -/
theorem foreign_witness {benv : Benv} {st : QueueState Record} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode q.call.target = k.code)
    (rep : Represents q.width q.words (storOf benv.state q.call.target) st)
    (hne : st.queue ≠ []) (fits : st.queue.length ≤ k.capN) {origin : Adr}
    (idx : Nat) (ty : UInt8) (rest : List (UInt8 × Adr)) (acc : List Bytes) (bal : BalBuilder) :
    let msg := foreignMsg benv q.call.target k.code origin
    msg.caller = systemAddress ∧ msg.tenv.stat.origin = origin ∧ msg.depth = 0 ∧
    ∃ post : Devm, Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok post)) ∧
      post.output = st.queue.flatMap q.out ∧ post.output ≠ [] ∧
      (drainedState k.capN k.shape.target.word st).queue = [] ∧
      Represents q.width q.words (storOf post.state q.call.target) (drainedState k.capN k.shape.target.word st) ∧
      (∃ out, processCheckedSystemTransaction (benv.withState benv.state) q.call.target [] =
          .ok (sysState k.shape benv.state q.call.target, out) ∧ out.returnData = post.output) ∧
      ∃ bal', runRequestContracts idx ((ty, q.call.target) :: rest) (benv.withState post.state) acc bal =
        runRequestContracts idx rest
          ((benv.withState post.state).withState (sysState k.shape post.state q.call.target)) acc bal' := by
  intro msg
  refine ⟨rfl, rfl, rfl, ?_⟩
  have hsf : (initSevm msg).benvStat.fork = .amsterdam := hfork
  have hle := SysPath.frameCost_le q.call.memory (initSevm msg) (initDevm msg)
  have hroom := q.call.bound_le
  have hr := q.call.room
  have hG : gCallStipend < systemTransactionGas - k.frameCost (initSevm msg) (initDevm msg) := by omega
  have hrun := q.records_miss_requests (benv := benv) (sevm := initSevm msg) (b := initDevm msg) (st := st)
    rfl hsf rfl rfl rfl rfl (foreign_ready hfork) hG hfork installed rep hne fits idx ty rest acc bal
  rw [show systemTransactionGas - k.frameCost (initSevm msg) (initDevm msg) +
      k.frameCost (initSevm msg) (initDevm msg) = systemTransactionGas by omega] at hrun
  exact hrun

end QueueCall

/-! ## What excludes it: any other caller -/

/-- The slots a submission writes at a tail below the word modulus are not the head. -/
theorem queueSlot_ne_head {width t j : Nat} (hb : queueBase width t + width ≤ 2 ^ 256) (hj : j < width) :
    queueSlot width t j ≠ 2 :=
  (queueSlot_ne (n := 2) (by omega) (by decide) hb hj).symm

theorem one_add_queueSlot (width t j : Nat) :
    (1 : B256) + queueSlot width t j = queueSlot width t (j + 1) := by
  rw [show (1 : B256) = Nat.toB256 1 by decide]
  exact record_key_add width t j 1

/-! ## The two contracts -/

namespace Deposit

open Creation (address)

/-- What the call returns on a queue, as the frame's output. -/
theorem call_output {benv : Benv} {st : QueueState Record} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code)
    (rep : Represents 6 Record.word (storOf benv.state address) st) :
    (SysPath.callPost sysPath benv address).output = (st.queue.take 64).flatMap Record.out := by
  obtain ⟨_, out, h, _, hr, _⟩ := system_call_fifo hfork installed rep
  have s : processCheckedSystemTransaction benv address [] =
      .ok (sysState sysShape benv.state address,
        systemCallOutputA (systemCallMsg benv address code []) (SysPath.callPost sysPath benv address)) :=
    (sysCall.spec hfork installed).1
  obtain rfl : systemCallOutputA (systemCallMsg benv address code []) (SysPath.callPost sysPath benv address) = out :=
    congrArg Prod.snd (Except.ok.inj (s.symm.trans h))
  exact hr

/-- The deposit call on a queue. -/
def queueCall : QueueCall sysPath Record where
  call := sysCall
  output := sysOutput
  width := 6
  words := Record.word
  out := Record.out
  next_eq := rfl
  out_ne := fun r h => by
    have := congrArg List.length h
    simp only [Record.out, List.length_append, List.length_reverse, List.length_nil] at this
    have lp := r.pubkey_length
    omega
  fifo := fun hfork installed rep => call_output hfork installed rep

/-- **The deposit builder's output length, from any storage.** The checked system call returns `184 * n` bytes
for the drain's count `n ≤ 64`. No storage premise. -/
theorem output_length {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) :
    ∃ post out n, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
      out.returnData.length = 184 * n ∧ n ≤ 64 ∧
      n = (drainCount 64 ((benv.state.getStor address).get 2) ((benv.state.getStor address).get 3)).toNat :=
  let ⟨post, out, h1, h2, h3⟩ := call_output_length sysCall sysOutput hfork installed
  ⟨post, out, _, h1, h2, h3, rfl⟩

/-- A submission does not write the head, at a tail below the word modulus. -/
theorem submittedStorage_head (sevm : Sevm) {s : Stor} {t : Nat} (ht : s.get 3 = t.toB256)
    (hb : queueBase 6 t + 6 ≤ 2 ^ 256) : (submittedStorage sevm s).get 2 = s.get 2 := by
  have key : submissionKey t.toB256 = queueSlot 6 t 0 := submissionKey_queueSlot t
  unfold submittedStorage
  dsimp only
  rw [ht, key, one_add_queueSlot, one_add_queueSlot, one_add_queueSlot, one_add_queueSlot, one_add_queueSlot,
    Stor.get_set_ne _ (by decide : (3 : B256) ≠ 2), Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)),
    Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)), Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)),
    Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)), Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)),
    Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)), Stor.get_set_ne _ (by decide : (1 : B256) ≠ 2)]

/-- **Any other caller cannot drain.** Under Amsterdam, a successful frame at the deposit code whose caller is not
SYSTEM leaves the head where it was, on storage representing a queue whose next record's slots fit below the word
modulus. So the premise that excludes the drain is the caller: `caller ≠ systemAddress`. -/
theorem non_system_keeps_head {sevm : Sevm} {pre post : Devm} {st : QueueState Record}
    (hcode : sevm.code = code) (hfork : sevm.benvStat.fork = .amsterdam) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory) (lengthBound : sevm.data.length < 2 ^ 256)
    (caller : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post))
    (rep : Represents 6 Record.word (fun key => (pre.getStor sevm.currentTarget).get key) st)
    (room : queueBase 6 st.tail + 6 ≤ 2 ^ 256) :
    (post.getStor sevm.currentTarget).get 2 = (pre.getStor sevm.currentTarget).get 2 := by
  cases UserFrames.exec_user_frame_amsterdam frames hcode hfork stack aligned wf lengthBound caller exec with
  | submission _ _ e =>
    rw [e.storage]
    exact submittedStorage_head sevm rep.tail room
  | feeRead _ _ _ e => rw [e.storage]

/-- `QueueCall.foreign_witness` at the deposit contract, on the one-record queue of `witness_state`, from any
state and at any Amsterdam environment. -/
theorem foreign_frame_witness {benv : Benv} (hfork : benv.stat.fork = .amsterdam) (origin : Adr) :
    ∃ σ : State, σ.getCode address = code ∧
      Represents 6 Record.word (storOf σ address) (witnessQueue witnessRecord) ∧
      let msg := foreignMsg (benv.withState σ) address code origin
      ∃ post : Devm, Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok post)) ∧
        post.output = witnessRecord.out ∧
        Represents 6 Record.word (storOf post.state address) (drainedState 64 8 (witnessQueue witnessRecord)) ∧
        (drainedState 64 8 (witnessQueue witnessRecord)).queue = [] := by
  obtain ⟨σ, hc, hrep⟩ := witness_state benv.state
  refine ⟨σ, hc, hrep, ?_⟩
  obtain ⟨-, -, -, post, he, ho, -, hq, hr, -⟩ := queueCall.foreign_witness (benv := benv.withState σ)
    (st := witnessQueue witnessRecord) hfork hc hrep (by decide) (by decide) (origin := origin) 0 0 [] [] {}
  refine ⟨post, he, ?_, hr, hq⟩
  rw [ho]
  exact List.append_nil _

end Deposit

namespace Exit

open Creation (address)

/-- What the call returns on a queue, as the frame's output. -/
theorem call_output {benv : Benv} {st : QueueState Record} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code)
    (rep : Represents 3 Record.word (storOf benv.state address) st) :
    (SysPath.callPost sysPath benv address).output = (st.queue.take 16).flatMap Record.out := by
  obtain ⟨_, out, h, _, hr, _⟩ := system_call_fifo hfork installed rep
  have s : processCheckedSystemTransaction benv address [] =
      .ok (sysState sysShape benv.state address,
        systemCallOutputA (systemCallMsg benv address code []) (SysPath.callPost sysPath benv address)) :=
    (sysCall.spec hfork installed).1
  obtain rfl : systemCallOutputA (systemCallMsg benv address code []) (SysPath.callPost sysPath benv address) = out :=
    congrArg Prod.snd (Except.ok.inj (s.symm.trans h))
  exact hr

/-- The exit call on a queue. -/
def queueCall : QueueCall sysPath Record where
  call := sysCall
  output := sysOutput
  width := 3
  words := Record.word
  out := Record.out
  next_eq := rfl
  out_ne := fun r h => by
    have := congrArg List.length h
    simp only [Record.out, List.length_append, List.length_nil] at this
    have lp := r.pubkey_length
    omega
  fifo := fun hfork installed rep => call_output hfork installed rep

/-- **The exit builder's output length, from any storage.** The checked system call returns `68 * n` bytes for
the drain's count `n ≤ 16`. No storage premise. -/
theorem output_length {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) :
    ∃ post out n, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
      out.returnData.length = 68 * n ∧ n ≤ 16 ∧
      n = (drainCount 16 ((benv.state.getStor address).get 2) ((benv.state.getStor address).get 3)).toNat :=
  let ⟨post, out, h1, h2, h3⟩ := call_output_length sysCall sysOutput hfork installed
  ⟨post, out, _, h1, h2, h3, rfl⟩

/-- A submission does not write the head, at a tail below the word modulus. -/
theorem submittedStorage_head (sevm : Sevm) {s : Stor} {t : Nat} (ht : s.get 3 = t.toB256)
    (hb : queueBase 3 t + 3 ≤ 2 ^ 256) : (submittedStorage sevm s).get 2 = s.get 2 := by
  have key : submissionKey t.toB256 = queueSlot 3 t 0 := record_key 3 t
  unfold submittedStorage
  dsimp only
  rw [ht, key, one_add_queueSlot, one_add_queueSlot,
    Stor.get_set_ne _ (by decide : (3 : B256) ≠ 2), Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)),
    Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)), Stor.get_set_ne _ (queueSlot_ne_head hb (by omega)),
    Stor.get_set_ne _ (by decide : (1 : B256) ≠ 2)]

/-- **Any other caller cannot drain.** Under Amsterdam, a successful frame at the exit code whose caller is not
SYSTEM leaves the head where it was, on storage representing a queue whose next record's slots fit below the word
modulus. So the premise that excludes the drain is the caller: `caller ≠ systemAddress`. -/
theorem non_system_keeps_head {sevm : Sevm} {pre post : Devm} {st : QueueState Record}
    (hcode : sevm.code = code) (hfork : sevm.benvStat.fork = .amsterdam) (stack : pre.stack = [])
    (aligned : pre.memory.size % 32 = 0) (wf : Mem.Wf pre.memory) (lengthBound : sevm.data.length < 2 ^ 256)
    (caller : sevm.caller ≠ systemAddress) (exec : Exec 0 sevm pre (.ok post))
    (rep : Represents 3 Record.word (fun key => (pre.getStor sevm.currentTarget).get key) st)
    (room : queueBase 3 st.tail + 3 ≤ 2 ^ 256) :
    (post.getStor sevm.currentTarget).get 2 = (pre.getStor sevm.currentTarget).get 2 := by
  cases UserFrames.exec_user_frame_amsterdam frames hcode hfork stack aligned wf lengthBound caller exec with
  | submission _ _ e =>
    rw [e.storage]
    exact submittedStorage_head sevm rep.tail room
  | feeRead _ _ _ e => rw [e.storage]

/-- `QueueCall.foreign_witness` at the exit contract, on the one-record queue of `witness_state`, from any state
and at any Amsterdam environment. -/
theorem foreign_frame_witness {benv : Benv} (hfork : benv.stat.fork = .amsterdam) (origin : Adr) :
    ∃ σ : State, σ.getCode address = code ∧
      Represents 3 Record.word (storOf σ address) witnessQueue ∧
      let msg := foreignMsg (benv.withState σ) address code origin
      ∃ post : Devm, Nonempty (Exec 0 (initSevm msg) (initDevm msg) (.ok post)) ∧
        post.output = witnessRecord.out ∧
        Represents 3 Record.word (storOf post.state address) (drainedState 16 2 witnessQueue) ∧
        (drainedState 16 2 witnessQueue).queue = [] := by
  obtain ⟨σ, hc, hrep⟩ := witness_state benv.state
  refine ⟨σ, hc, hrep, ?_⟩
  obtain ⟨-, -, -, post, he, ho, -, hq, hr, -⟩ := queueCall.foreign_witness (benv := benv.withState σ)
    (st := witnessQueue) hfork hc hrep (by decide) (by decide) (origin := origin) 0 0 [] [] {}
  refine ⟨post, he, ?_, hr, hq⟩
  rw [ho]
  exact List.append_nil _

end Exit

end Blanc.Lift.BuilderRequest
