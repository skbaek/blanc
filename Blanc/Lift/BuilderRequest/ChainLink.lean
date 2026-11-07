import Batteries.Tactic.OpenPrivate
import Blanc.ExecutionKeptChain
import Blanc.Lift.BuilderRequest.Delivery
import Blanc.Lift.SystemCallAmsterdam

/-!
# From a chain's history to the delivery sequence

`Delivery` takes a list of frames at a builder contract as its input. This module produces that list from a history:
the frames kept at the contract, in order. A user frame goes through the contract's frame laws; a request step at the
contract is one kept root with the system caller, and is the request phase's `system` frame.

Retention only: no statement names a gas amount, a settlement amount or a frame that did not commit.
-/

namespace Blanc.Lift.BuilderRequest.ChainLink

open Jaune ExecutionTrace Delivery

open private runPrepared_cases from Blanc.ExecutionKeptTop
open private prepare_system from Blanc.Lift.SystemCallAmsterdam
open private runPreparedTopFrame msgCallOutputAmsterdam from Jaune.Transaction
open private withdrawalsPass_getCode withdrawalsPass_requests from Blanc.ExecutionKeptChain

/-! ## What a contract brings -/

/-- A fact of every kept fork, from the covered forks' list and Amsterdam. -/
theorem _root_.Blanc.KeptFork.forall {P : Fork → Prop} (covered : ∀ f ∈ coveredForks, P f) (amsterdam : P .amsterdam) :
    ∀ f, KeptFork f → P f := by
  rintro f (hf | rfl)
  · exact covered f hf
  · exact amsterdam

/-- Where a builder contract sits among the addresses the block's own calls use. -/
structure Placed (a : Adr) : Prop where
  /-- No kept fork runs a precompile there. -/
  precompile : ∀ f, KeptFork f → ¬ f.ruleSet.isPrecomp a
  /-- It is not the beacon-roots contract. -/
  beacon : beaconRootsAddress ≠ a
  /-- It is not the history contract. -/
  history : historyStorageAddress ≠ a

/-- What the chain link needs of a builder contract, beyond its frame laws in `Contract`. `ty` is its request type. -/
structure Linked (c : Contract) (ty : UInt8) where
  /-- The contract's user frames. -/
  frames : UserFrames
  /-- They are frames of its code. -/
  code_eq : frames.code = c.code
  /-- A user frame is a submission or a fee read on empty calldata. -/
  classify : ∀ {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}, frames.Frame l pre post →
    (∃ i o, c.Submitted l pre post i o) ∨ (sevm.data = [] ∧ ∃ i o, UserPath.FeeReadOn l c.target pre post i o)
  /-- The code runs: it is nonempty and no delegation. -/
  runnable : c.code.toList ≠ [] ∧ ¬ isValidDelegation c.code
  /-- The address is free of the block's other calls. -/
  placed : Placed c.address
  /-- A submission has calldata, so a fee read or a request call is no submission. -/
  payload_ne : c.payload ≠ 0
  /-- The type byte is not the deposit log's. -/
  ty_ne : ty ≠ 0
  /-- Amsterdam's list holds the address exactly once, with this type byte, and nothing else with it. -/
  listed : amsterdamRequests.filter (fun p => p.1 == ty || p.2 == c.address) = [(ty, c.address)]
  /-- The covered forks' lists hold neither. -/
  unlisted : ∀ f, CoveredFork f → ∀ p ∈ f.ruleSet.requests, p.1 ≠ ty ∧ p.2 ≠ c.address

/-! ## Observers -/

/-- The record a kept frame at the contract submits: calldata of the submission's length gives one, and nothing else
does, so a fee read and a request call give none. -/
def submittedBy (c : Contract) (f : Exec.Frame) : Option c.Record :=
  if h : f.sevm.data.length = c.payload then some (c.recordOf f.sevm h) else none

/-- What a kept frame does to the queue model. -/
def keptEvent (c : Contract) (f : Exec.Frame) : Event c.Record :=
  match submittedBy c f with
  | some r => .submission r
  | none => if f.sevm.caller = systemAddress then .system false else .feeRead

/-- The bytes of one request entry after its type byte, if that byte is `ty`. -/
def entryOf (ty : UInt8) : Bytes → Option Bytes
  | [] => none
  | t :: tail => if t = ty then some tail else none

/-- The bytes of type `ty` in one block's requests. -/
def blockDelivered (ty : UInt8) (b : KeptBlock) : Bytes := (b.output.requests.filterMap (entryOf ty)).flatten

/-- The bytes of type `ty` a history's blocks output, in order. -/
def delivered (ty : UInt8) (blocks : List KeptBlock) : Bytes := blocks.flatMap (blockDelivered ty)

namespace History

/-- The frames a history keeps at `a`, in order. -/
def kept (a : Adr) (blocks : List KeptBlock) : List Exec.Frame := blocks.flatMap (KeptBlock.keptAt a)

/-- The records a history's kept frames submit, in order. -/
def submitted (c : Contract) (blocks : List KeptBlock) : List c.Record :=
  (kept c.address blocks).filterMap (submittedBy c)

/-- All the value a history's kept frames at `a` carry. -/
def paid (a : Adr) (blocks : List KeptBlock) : Nat := ((kept a blocks).map fun f => f.sevm.value.toNat).sum

/-- No transaction in the history was sent by `S`. -/
def NoSender (S : Adr) (blocks : List KeptBlock) : Prop := ∀ b ∈ blocks, NoSenderAt S b.run.senders

/-- No authorization in the history recovers to `S`. -/
def NoAuthority (S : Adr) (blocks : List KeptBlock) : Prop := ∀ b ∈ blocks, NoAuthorityAt S b.run.senders

/-- No frame the history keeps creates at `S`. -/
def NoCreate (S : Adr) (blocks : List KeptBlock) : Prop := ∀ b ∈ blocks, NoCreateAt S b.run.roots

/-- Every transaction's calldata in the history is word-sized. -/
def DataWords (blocks : List KeptBlock) : Prop := ∀ b ∈ blocks, DataFits b.run.senders

end History

/-- What a request step at `a` returns, and nothing for a step elsewhere. -/
def stepOutput (a : Adr) (s : RequestStep) : Bytes := if s.target = a then s.output.returnData else []

variable {c : Contract} {ty : UInt8}

theorem keptEvent_of_length {f : Exec.Frame} (h : f.sevm.data.length = c.payload) :
    keptEvent c f = .submission (c.recordOf f.sevm h) := by
  unfold keptEvent submittedBy
  rw [dite_eq_left h]

theorem keptEvent_user {f : Exec.Frame} (h : ¬ f.sevm.data.length = c.payload) (caller : f.sevm.caller ≠ systemAddress) :
    keptEvent c f = .feeRead := by
  unfold keptEvent submittedBy
  rw [dite_eq_right h]
  exact ite_eq_right caller

theorem keptEvent_system {f : Exec.Frame} (h : ¬ f.sevm.data.length = c.payload)
    (caller : f.sevm.caller = systemAddress) : keptEvent c f = .system false := by
  unfold keptEvent submittedBy
  rw [dite_eq_right h]
  exact ite_eq_left caller

/-! ## The correspondence -/

/-- A sequence frame is this kept frame: the same storage before and after, the event the kept frame determines, and
no more value than it carries. -/
structure Matches (c : Contract) (g : Delivery.Frame c) (f : Exec.Frame) : Prop where
  before : g.before = Devm.getStor f.pre c.address
  after : g.after = Devm.getStor f.post c.address
  event : g.event = keptEvent c f
  value : g.value ≤ f.sevm.value.toNat

/-- The sequence's frames are the kept frames, one for one, in order. -/
def Corresponds (c : Contract) (frames : List (Delivery.Frame c)) (kept : List Exec.Frame) : Prop :=
  List.Forall₂ (Matches c) frames kept

theorem Corresponds.chain {frames : List (Delivery.Frame c)} {kept : List Exec.Frame} (h : Corresponds c frames kept)
    {s t : Stor} (chain : KeptChain c.address s kept t) : Chain s frames t := by
  induction h generalizing s with
  | nil =>
      cases chain
      exact .nil _
  | cons m _ ih =>
      cases chain with
      | cons starts tail => exact .cons (m.before.trans starts) (m.after ▸ ih tail)

/-- **The sequence's submissions are what the kept frames submit.** -/
theorem Corresponds.submissions {frames : List (Delivery.Frame c)} {kept : List Exec.Frame}
    (h : Corresponds c frames kept) : Delivery.submissions frames = kept.filterMap (submittedBy c) := by
  induction h with
  | nil => rfl
  | @cons g f gs fs m _ ih =>
      change submitted (g.event :: events gs) = _
      rw [m.event, List.filterMap_cons]
      unfold keptEvent
      cases hs : submittedBy c f with
      | none =>
          dsimp only
          split
          · exact ih
          · exact ih
      | some r =>
          dsimp only
          change r :: Delivery.submissions gs = _
          rw [ih]

/-- The sequence has no system call but the request phase's. -/
theorem Corresponds.requestPhase {frames : List (Delivery.Frame c)} {kept : List Exec.Frame}
    (h : Corresponds c frames kept) : RequestPhaseOnly frames := by
  induction h with
  | nil =>
      intro f hf
      cases hf
  | @cons g f gs fs m _ ih =>
      intro x hx latch he
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [m.event] at he
        unfold keptEvent at he
        split at he
        · cases he
        · split at he
          · cases he
            rfl
          · cases he
      · exact ih x hx latch he

/-- The sequence's value is at most the kept frames'. -/
theorem Corresponds.value_le {frames : List (Delivery.Frame c)} {kept : List Exec.Frame}
    (h : Corresponds c frames kept) :
    (frames.map Delivery.Frame.value).sum ≤ (kept.map fun f => f.sevm.value.toNat).sum := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons m _ ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add m.value ih

/-- The kept frames have a sequence, with this output. -/
def Mapped (c : Contract) (kept : List Exec.Frame) (output : Bytes) : Prop :=
  ∃ frames, Corresponds c frames kept ∧ systemOutput frames = output

theorem Mapped.nil : Mapped c [] [] := ⟨[], .nil, rfl⟩

theorem Mapped.append {xs ys : List Exec.Frame} {o p : Bytes} (first : Mapped c xs o) (second : Mapped c ys p) :
    Mapped c (xs ++ ys) (o ++ p) := by
  obtain ⟨gs, h, rfl⟩ := first
  obtain ⟨hs, k, rfl⟩ := second
  refine ⟨gs ++ hs, ?_, by simp only [systemOutput, List.flatMap_append]⟩
  induction h with
  | nil => exact k
  | cons m _ ih => exact .cons m ih

/-! ## A user frame -/

private theorem Frame.ofUser (L : Linked c ty) {sevm : Sevm} {l : StorageSteps sevm} {pre post : Devm}
    {run : Exec 0 sevm pre (.ok post)} {committed : Execution.commits (.ok post) = true} (rules : UserRules l)
    (target : sevm.currentTarget = c.address) (caller : sevm.caller ≠ systemAddress)
    (law : L.frames.Frame l pre post) :
    ∃ g : Delivery.Frame c, Matches c g ⟨0, sevm, pre, .ok post, run, committed⟩ := by
  rcases L.classify law with ⟨i, o, sub⟩ | ⟨empty, i, o, read⟩
  · refine ⟨.submission sevm pre post l i o rules target caller sub, rfl, rfl, ?_, Nat.le_refl _⟩
    exact (keptEvent_of_length (f := ⟨0, sevm, pre, .ok post, run, committed⟩) (c.length sub)).symm
  · refine ⟨.feeRead sevm pre post l i o rules target caller read, rfl, rfl, ?_, Nat.le_refl _⟩
    refine (keptEvent_user (f := ⟨0, sevm, pre, .ok post, run, committed⟩) ?_ caller).symm
    change ¬ sevm.data.length = c.payload
    rw [empty]
    exact fun same => L.payload_ne same.symm

/-- **A kept user frame is a sequence frame.** A frame kept at the contract, at a kept fork, with a caller other than
the system: its frame law makes it a submission or a fee read, on the storage it found and left, with its event. -/
theorem Frame.ofKept (L : Linked c ty) {f : Exec.Frame} {stat : BenvStat}
    (entry : Exec.Frame.EntryIn c.address c.code stat f) (fork : KeptFork stat.fork)
    (caller : f.sevm.caller ≠ systemAddress) : ∃ g : Delivery.Frame c, Matches c g f := by
  obtain ⟨orig, e⟩ := entry
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := f
  obtain ⟨hpc, target, code, stack, size, wf, hstat, dlen⟩ := e
  dsimp only at hpc target code stack size wf hstat dlen caller
  subst hpc
  cases out with
  | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
      have hfork : sevm.benvStat.fork = stat.fork := by rw [hstat]
      have hcode : sevm.code = L.frames.code := code.trans L.code_eq.symm
      rcases fork with covered | amsterdam
      · have hc : CoveredFork sevm.benvStat.fork := by rw [hfork]; exact covered
        exact Frame.ofUser L (.covered hc) target caller
          (L.frames.exec_user_frame hcode hc stack size wf dlen caller run)
      · have ha : sevm.benvStat.fork = .amsterdam := hfork.trans amsterdam
        exact Frame.ofUser L (.amsterdam ha) target caller
          (L.frames.exec_user_frame_amsterdam hcode ha stack size wf dlen caller run)

/-- Kept frames with a caller other than the system have a sequence with no output. -/
theorem Mapped.ofUsers (L : Linked c ty) {kept : List Exec.Frame} {stat : BenvStat}
    (entries : ∀ f ∈ kept, Exec.Frame.EntryIn c.address c.code stat f) (fork : KeptFork stat.fork)
    (callers : ∀ f ∈ kept, f.sevm.caller ≠ systemAddress) : Mapped c kept [] := by
  induction kept with
  | nil => exact .nil
  | cons f rest ih =>
      obtain ⟨g, m⟩ := Frame.ofKept L (entries f List.mem_cons_self) fork (callers f List.mem_cons_self)
      obtain ⟨gs, h, out⟩ := ih (fun x hx => entries x (List.mem_cons_of_mem _ hx))
        (fun x hx => callers x (List.mem_cons_of_mem _ hx))
      refine ⟨g :: gs, .cons m h, ?_⟩
      have user : g.output = [] := g.output_user fun latch he => by
        rw [m.event] at he
        unfold keptEvent at he
        split at he
        · cases he
        · rw [ite_eq_right (callers f List.mem_cons_self)] at he
          cases he
      change g.output ++ systemOutput gs = []
      rw [user, out]
      rfl

/-! ## A request step -/

theorem keptChain_nil {a : Adr} {s t : Stor} (h : KeptChain a s [] t) : s = t := by
  cases h
  rfl

/-- **A request step at a builder contract is exactly one kept root.** Under Amsterdam, a checked system call of code
that is no delegation, at an address no precompile holds, runs one root; it commits, since the checked call had no
error, and it is all the call keeps there. -/
theorem request_step_root {benv : Benv} {a : Adr} {post : State} {out : MsgCallOutput} {rs : List Root}
    (hfork : benv.stat.fork = .amsterdam) (hc : (benv.state.getCode a).toList ≠ [])
    (hd : ¬ isValidDelegation (benv.state.getCode a)) (hp : ¬ amsterdamRules.isPrecomp a)
    (run : processCheckedSystemTransaction benv a [] = .ok (post, out))
    (roots : MessageRoots (systemTransactionMessage benv a []) post out rs) :
    ∃ f, rs.flatMap (Root.keptAt a) = [f] ∧ f.sevm.caller = systemAddress ∧ f.sevm.data = [] ∧
      Devm.getStor f.pre a = benv.state.getStor a ∧ Devm.getStor f.post a = post.getStor a := by
  obtain ⟨noError, -⟩ := exists_systemRoots run
  have hdel : getDelegatedCodeAddress (benv.state.getCode a) = none := by
    simp only [getDelegatedCodeAddress, hd, ↓reduceIte]
  have hprep : prepareTopLevelAmsterdam amsterdamStateGasRules (systemTransactionMessage benv a []) =
      .ok (systemTransactionMessage benv a [], systemCallBase (systemTransactionMessage benv a [])) :=
    prepare_system hfork rfl hdel
  have hsg : (systemTransactionMessage benv a []).benv.stat.rules.stateGas = some amsterdamStateGasRules :=
    amsterdam_stateGas (s := (systemTransactionMessage benv a []).benv.stat) hfork
  have hm := roots.1
  unfold processMessageCall at hm
  simp only [show (systemTransactionMessage benv a []).target.isNone = false from rfl, Bool.false_eq_true,
    ↓reduceIte] at hm
  unfold processMessageCall.call at hm
  rw [hsg] at hm
  simp only at hm
  unfold processTopLevelAmsterdam at hm
  rw [hprep] at hm
  dsimp only at hm
  obtain ⟨s, hevm, hout⟩ := Except.bind_eq_ok hm
  have hrun : runPreparedTopFrame (Frame.ofCall (systemTransactionMessage benv a []))
      (systemCallBase (systemTransactionMessage benv a [])) = .ok s := Except.bimap_id_eq_ok hevm
  have herr : s.error = out.error := by
    unfold msgCallOutputAmsterdam at hout
    dsimp only at hout
    split at hout <;>
    · obtain ⟨_, _, hlast⟩ := Except.bind_eq_ok hout
      simp only [Except.ok.injEq, Prod.mk.injEq] at hlast
      rw [← hlast.2]
  have ht : (Frame.ofCall (systemTransactionMessage benv a [])).inner.benvAfterTransfer =
      .ok (systemTransactionMessage benv a []).benv := Msg.benvAfterTransfer_of_value_zero rfl
  have hnot : ¬ (systemTransactionMessage benv a []).benv.stat.rules.isPrecomp a := by
    rw [amsterdam_rules (s := (systemTransactionMessage benv a []).benv.stat) hfork]
    exact hp
  have hentry : messageEntry (systemTransactionMessage benv a []) =
      preparedEntry (Frame.ofCall (systemTransactionMessage benv a []))
        (systemCallBase (systemTransactionMessage benv a [])) := by
    unfold messageEntry
    rw [hsg]
    dsimp only
    unfold amsterdamEntry
    rw [hprep]
    rfl
  rcases runPrepared_cases ht hrun with ⟨hnone, adr, -⟩ | ⟨hsome, hs⟩
  · unfold preparedEntry at hnone
    rw [ht] at hnone
    dsimp only at hnone
    have enter : executeCode.enter ((Frame.ofCall (systemTransactionMessage benv a [])).inner.withBenv
        (systemTransactionMessage benv a []).benv) = .inl (initEvm ((Frame.ofCall (systemTransactionMessage benv a
          [])).inner.withBenv (systemTransactionMessage benv a []).benv)) := by
      have hcond : ¬ ((!false && decide ((systemTransactionMessage benv a []).benv.stat.rules.isPrecomp a)) = true) := by
        rw [decide_eq_false hnot]
        decide
      exact ite_eq_right hcond
    rw [enter] at hnone
    cases hnone
  · have hmap := roots.2
    rw [hentry, hsome] at hmap
    cases rs with
    | nil => cases hmap
    | cons r tail =>
        simp only [Option.toList_some, List.map_cons, List.cons.injEq, Prod.mk.injEq, List.map_eq_nil_iff] at hmap
        obtain ⟨⟨hf, he⟩, rfl⟩ := hmap
        have mem : r ∈ [r] := List.mem_singleton.mpr rfl
        have hraw := (roots.mem_entry mem).2
        have settles : Frame.settlementCommits r.frame r.raw = true := by
          unfold Frame.settlementCommits
          rw [← hraw, he, hf, hs]
          dsimp only
          rw [herr, noError]
          rfl
        obtain ⟨hcaller, here, -, hdata⟩ := roots.entry_routing mem
        have keep : Root.keptAt a r =
            [Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits settles)] := by
          rw [Root.keptAt, dite_eq_left settles, ite_eq_left (show r.evm.sta.currentTarget = a from here)]
        have flat : [r].flatMap (Root.keptAt a) =
            [Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits settles)] := by
          rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, keep]
        refine ⟨_, flat, hcaller, hdata, (roots.entry_kept mem hc hd).2, ?_⟩
        have chain := (roots.chain (a := a) hc hd).1
        rw [flat] at chain
        cases chain with
        | cons starts rest => exact keptChain_nil rest

/-- A request step at the contract is one kept root, and the request phase's `system` frame, with the output it
returned. -/
theorem Mapped.ofRequestStep (L : Linked c ty) {benv : Benv} {post : State} {out : MsgCallOutput} {rs : List Root}
    (hfork : benv.stat.fork = .amsterdam) (code : benv.state.getCode c.address = c.code)
    (run : processCheckedSystemTransaction benv c.address [] = .ok (post, out))
    (roots : MessageRoots (systemTransactionMessage benv c.address []) post out rs) :
    Mapped c (rs.flatMap (Root.keptAt c.address)) out.returnData := by
  obtain ⟨f, flat, caller, data, before, after⟩ := request_step_root hfork (by rw [code]; exact L.runnable.1)
    (by rw [code]; exact L.runnable.2) (L.placed.precompile _ (.inr rfl)) run roots
  rw [flat]
  refine ⟨[.system benv [] post out hfork code (by decide) run], .cons ⟨before.symm, after.symm, ?_, Nat.zero_le _⟩ .nil,
    by simp only [systemOutput, List.flatMap_cons, List.flatMap_nil, List.append_nil]; rfl⟩
  refine (keptEvent_system ?_ caller).symm
  rw [data]
  exact fun same => L.payload_ne same.symm

/-- **The request fold, as a sequence.** Each step at the contract is its `system` frame; a step elsewhere keeps only
user frames there. -/
theorem Mapped.ofRequestRoots (L : Linked c ty) {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv}
    {acc acc' : List Bytes} {bal bal' : BalBuilder} {final : State} {steps : List RequestStep}
    (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) (fork : KeptFork benv.stat.fork)
    (code : benv.state.getCode c.address = c.code)
    (onlyAmsterdam : ∀ p ∈ contracts, p.2 = c.address → benv.stat.fork = .amsterdam)
    (others : ∀ s ∈ steps, s.target ≠ c.address → ∀ f ∈ s.roots.flatMap (Root.keptAt c.address),
      f.sevm.caller ≠ systemAddress)
    (entries : ∀ f ∈ (requestRootsOf steps).flatMap (Root.keptAt c.address),
      Exec.Frame.EntryIn c.address c.code benv.stat f) :
    Mapped c ((requestRootsOf steps).flatMap (Root.keptAt c.address)) (steps.flatMap (stepOutput c.address)) := by
  induction h with
  | nil benv acc bal => exact .nil
  | @cons type target rest benv acc acc' bal bal' post final out rs steps hcall roots tail ih =>
      have split : (requestRootsOf (⟨type, target, post, out, rs⟩ :: steps)).flatMap (Root.keptAt c.address) =
          rs.flatMap (Root.keptAt c.address) ++ (requestRootsOf steps).flatMap (Root.keptAt c.address) := by
        unfold requestRootsOf
        rw [List.flatMap_cons, List.flatMap_append]
      have hc : (benv.state.getCode c.address).toList ≠ [] := by rw [code]; exact L.runnable.1
      have hd : ¬ isValidDelegation (benv.state.getCode c.address) := by rw [code]; exact L.runnable.2
      have code' : post.getCode c.address = benv.state.getCode c.address := (MessageRoots.chain roots hc hd).2
      rw [split] at entries ⊢
      rw [List.flatMap_cons]
      have below := ih fork (code'.trans code)
        (fun p hp => onlyAmsterdam p (List.mem_cons_of_mem _ hp))
        (fun s hs => others s (List.mem_cons_of_mem _ hs))
        (fun f hf => entries f (List.mem_append_right _ hf))
      refine Mapped.append ?_ below
      by_cases here : target = c.address
      · subst here
        have hfork := onlyAmsterdam _ List.mem_cons_self rfl
        have one := Mapped.ofRequestStep L hfork code hcall roots
        have same : stepOutput c.address ⟨type, c.address, post, out, rs⟩ = out.returnData := ite_eq_left rfl
        rw [same]
        exact one
      · have same : stepOutput c.address ⟨type, target, post, out, rs⟩ = [] := ite_eq_right here
        rw [same]
        exact Mapped.ofUsers L (fun f hf => entries f (List.mem_append_left _ hf)) fork
          (others _ List.mem_cons_self here)

/-! ## The request bytes -/

theorem steps_entries {ty : UInt8} {a : Adr} {steps : List RequestStep} (typed : ∀ s ∈ steps, s.type = ty ↔ s.target = a) :
    ((steps.flatMap RequestStep.bytes).filterMap (entryOf ty)).flatten = steps.flatMap (stepOutput a) := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
      rw [List.flatMap_cons, List.flatMap_cons, List.filterMap_append, List.flatten_append,
        ih fun x hx => typed x (List.mem_cons_of_mem _ hx)]
      congr 1
      have hs := typed s List.mem_cons_self
      unfold RequestStep.bytes stepOutput
      split
      · by_cases here : s.target = a
        · simp only [List.singleton_append, List.filterMap_cons, List.filterMap_nil, entryOf, hs.mpr here,
            ↓reduceIte, List.flatten_cons, List.flatten_nil, List.append_nil, here]
        · have ne : ¬ s.type = ty := fun same => here (hs.mp same)
          simp only [List.singleton_append, List.filterMap_cons, List.filterMap_nil, entryOf, ne, ↓reduceIte,
            List.flatten_nil, here]
      · rename_i empty
        have nil : s.output.returnData = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_not_pos empty)
        simp only [List.filterMap_nil, List.flatten_nil, nil, ite_self]

/-- Under a kept fork a request's type is the contract's exactly when its target is. -/
theorem Linked.typed (L : Linked c ty) {f : Fork} (fork : KeptFork f) (p : UInt8 × Adr)
    (hp : p ∈ f.ruleSet.requests) : p.1 = ty ↔ p.2 = c.address := by
  rcases fork with covered | rfl
  · exact ⟨fun e => absurd e (L.unlisted f covered p hp).1, fun e => absurd e (L.unlisted f covered p hp).2⟩
  · have key : (p.1 = ty ∨ p.2 = c.address) → p = (ty, c.address) := by
      intro either
      have mem : p ∈ amsterdamRequests.filter (fun p => p.1 == ty || p.2 == c.address) :=
        List.mem_filter.mpr ⟨hp, by simp only [Bool.or_eq_true, beq_iff_eq]; exact either⟩
      rw [L.listed] at mem
      exact List.mem_singleton.mp mem
    exact ⟨fun e => by rw [key (.inl e)], fun e => by rw [key (.inr e)]⟩

/-- A kept fork lists the contract only at Amsterdam. -/
theorem Linked.onlyAmsterdam (L : Linked c ty) {f : Fork} (fork : KeptFork f) (p : UInt8 × Adr)
    (hp : p ∈ f.ruleSet.requests) (here : p.2 = c.address) : f = .amsterdam := by
  rcases fork with covered | rfl
  · exact absurd here (L.unlisted f covered p hp).2
  · rfl

section Body

variable {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal} {state : State}
  {bout : BlockOutput} {run : BodyRun}

/-- **A block's requests of type `ty` are what the request steps at the contract returned.** The deposit log's entry
has type byte 0, which is not `ty`. -/
theorem block_entries (L : Linked c ty) (h : BodyRoots benv txs ommers wds state bout run)
    (fork : KeptFork benv.stat.fork) :
    (bout.requests.filterMap (entryOf ty)).flatten = run.requests.flatMap (stepOutput c.address) := by
  by_cases on : benv.stat.rules.header.requestsHash = true
  · obtain ⟨deposits, -, eq⟩ := h.requests_eq on
    have typed : ∀ s ∈ run.requests, s.type = ty ↔ s.target = c.address := fun s hs =>
      L.typed fork (s.type, s.target) (by
        have := h.contracts_eq on
        change benv.stat.fork.ruleSet.requests = _ at this
        rw [this]
        exact List.mem_map_of_mem hs)
    rw [eq, List.filterMap_append, List.flatten_append, steps_entries typed]
    have zero : ¬ (0 : UInt8) = ty := fun same => L.ty_ne same.symm
    split
    · simp only [depositRequestType, List.singleton_append, List.filterMap_cons, List.filterMap_nil, entryOf, zero,
        ↓reduceIte, List.flatten_nil, List.nil_append]
    · rfl
  · obtain ⟨st, out, pass, -, requests⟩ := h.stages
    obtain ⟨decoded, -, roots⟩ := h.transactions
    have off : ¬ (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut
        wds).1).stat.rules.header.requestsHash = true := by
      change ¬ run.txEnv.stat.rules.header.requestsHash = true
      rw [h.txEnv_stat]
      exact on
    unfold RequestPass at pass
    rw [ite_eq_right off] at pass
    have nil : bout.requests = [] := by
      rw [requests, pass.2.1]
      exact (withdrawalsPass_requests _ _ _ _).trans roots.requests_eq
    rw [nil, pass.2.2]
    rfl

/-- **A body's kept frames at the contract, as a sequence.** Outside the request fold they are user frames; the fold
is `Mapped.ofRequestRoots`. -/
theorem Mapped.ofBody (L : Linked c ty) (h : BodyRoots benv txs ommers wds state bout run)
    (rules : KeptRules benv.stat.rules) (fork : KeptFork benv.stat.fork)
    (code : benv.state.getCode c.address = c.code) (created : c.address ∉ benv.createdAccounts)
    (outside : ∀ f ∈ run.outsideRequests c.address, f.sevm.caller ≠ systemAddress)
    (others : ∀ s ∈ run.requests, s.target ≠ c.address → ∀ f ∈ s.roots.flatMap (Root.keptAt c.address),
      f.sevm.caller ≠ systemAddress)
    (entries : ∀ f ∈ run.roots.flatMap (Root.keptAt c.address), Exec.Frame.EntryIn c.address c.code benv.stat f) :
    Mapped c (run.roots.flatMap (Root.keptAt c.address)) (run.requests.flatMap (stepOutput c.address)) := by
  have split : run.roots.flatMap (Root.keptAt c.address) = run.outsideRequests c.address ++
      (requestRootsOf run.requests).flatMap (Root.keptAt c.address) := by
    unfold BodyRun.roots BodyRun.outsideRequests
    rw [List.flatMap_append]
  rw [split] at entries ⊢
  have first : Mapped c (run.outsideRequests c.address) [] :=
    Mapped.ofUsers L (fun f hf => entries f (List.mem_append_left _ hf)) fork outside
  have second : Mapped c ((requestRootsOf run.requests).flatMap (Root.keptAt c.address))
      (run.requests.flatMap (stepOutput c.address)) := by
    obtain ⟨st, out, pass, -, -⟩ := h.stages
    obtain ⟨decoded, -, roots⟩ := h.transactions
    have hs : run.txEnv.stat = benv.stat := h.txEnv_stat
    by_cases on : benv.stat.rules.header.requestsHash = true
    · have on' : (run.txEnv.withState (withdrawalsPass benv.stat.rules run.txEnv run.txOut
          wds).1).stat.rules.header.requestsHash = true := by
        change run.txEnv.stat.rules.header.requestsHash = true
        rw [hs]
        exact on
      unfold RequestPass at pass
      rw [ite_eq_left on'] at pass
      obtain ⟨deposits, acc, bal, -, fold, -⟩ := pass
      have hc : (benv.state.getCode c.address).toList ≠ [] := by rw [code]; exact L.runnable.1
      have hd : ¬ isValidDelegation (benv.state.getCode c.address) := by rw [code]; exact L.runnable.2
      have code₁ := (h.pre.chain hc hd).2
      have code₂ := (roots.chain rules (a := c.address) (by simpa only [Benv.withState, code₁] using hc)
        (by simpa only [Benv.withState, code₁] using hd) created).2
      refine Mapped.ofRequestRoots L fold ?_
        ((withdrawalsPass_getCode _ _ _ _ c.address).trans (code₂.trans (code₁.trans code))) ?_ others ?_
      · change KeptFork run.txEnv.stat.fork
        rw [hs]
        exact fork
      · intro p hp here
        change run.txEnv.stat.fork = .amsterdam
        rw [hs]
        refine L.onlyAmsterdam fork p ?_ here
        change p ∈ run.txEnv.stat.fork.ruleSet.requests at hp
        rw [hs] at hp
        exact hp
      · intro f hf
        change Exec.Frame.EntryIn c.address c.code run.txEnv.stat f
        rw [hs]
        exact entries f (List.mem_append_right _ hf)
    · rw [h.requests_off on]
      exact .nil
  exact first.append second

end Body

/-! ## The history -/

section History

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- The history's kept frames at the contract have a sequence, whose output is the blocks' requests of type `ty`. -/
theorem Mapped.ofHistory (L : Linked c ty) (h : KeptHistory cfg start blocks stop)
    (code : start.state.getCode c.address = c.code)
    (outside : ∀ b ∈ blocks, ∀ f ∈ b.run.outsideRequests c.address, f.sevm.caller ≠ systemAddress)
    (others : ∀ b ∈ blocks, ∀ s ∈ b.run.requests, s.target ≠ c.address →
      ∀ f ∈ s.roots.flatMap (Root.keptAt c.address), f.sevm.caller ≠ systemAddress)
    (entries : ∀ b ∈ blocks, ∀ f ∈ b.keptAt c.address, Exec.Frame.EntryIn c.address c.code b.benv.stat f) :
    Mapped c (History.kept c.address blocks) (delivered ty blocks) := by
  have hc : (start.state.getCode c.address).toList ≠ [] := by rw [code]; exact L.runnable.1
  have hd : ¬ isValidDelegation (start.state.getCode c.address) := by rw [code]; exact L.runnable.2
  induction h with
  | refl => exact .nil
  | @step blocks b post prior step ih =>
      have mem : b ∈ blocks ++ [b] := List.mem_append_right _ List.mem_cons_self
      have below := ih (fun x hx => outside x (List.mem_append_left _ hx))
        (fun x hx => others x (List.mem_append_left _ hx)) (fun x hx => entries x (List.mem_append_left _ hx))
      have one := Mapped.ofBody L step.body step.kept.rules step.kept ((prior.chain hc hd).2.trans code)
        AdrSet.not_mem_empty (outside b mem) (others b mem) (entries b mem)
      rw [← block_entries L step.body step.kept] at one
      unfold History.kept delivered
      rw [List.flatMap_append, List.flatMap_append, List.flatMap_singleton, List.flatMap_singleton]
      exact below.append one

/-- **The proof-level form.** The frames a history keeps at the contract are a chain of the delivery sequence, one for
one, and the sequence's output is the blocks' requests of type `ty`. So `Chain.delivered`, and each contract's
`delivery`, `excess_dynamics` and `later_quote`, hold of the history. -/
theorem history_chain (L : Linked c ty) (h : KeptHistory cfg start blocks stop)
    (code : start.state.getCode c.address = c.code) (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (data : History.DataWords blocks) :
    ∃ frames, Chain (start.state.getStor c.address) frames (stop.state.getStor c.address) ∧
      Corresponds c frames (History.kept c.address blocks) ∧ systemOutput frames = delivered ty blocks := by
  have hc : (start.state.getCode c.address).toList ≠ [] := by rw [code]; exact L.runnable.1
  have hd : ¬ isValidDelegation (start.state.getCode c.address) := by rw [code]; exact L.runnable.2
  obtain ⟨outside, others, -⟩ := h.caller_ne (a := c.address) empty L.placed.beacon L.placed.history senders authorities
    creates
  obtain ⟨frames, corr, out⟩ := Mapped.ofHistory (ty := ty) L h code outside others
    (h.entry_in code L.runnable.1 L.runnable.2 data)
  exact ⟨frames, corr.chain (h.chain hc hd).1, corr, out⟩

/-- A prefix of a list has the prefix of its bytes. -/
theorem take_flatMap_prefix {α : Type} (out : α → Bytes) (xs : List α) (k : Nat) :
    (xs.take k).flatMap out <+: xs.flatMap out :=
  ⟨(xs.drop k).flatMap out, by rw [← List.flatMap_append, List.take_append_drop]⟩

/-- **Delivery over a history.** From a represented queue, with the word range over what the history submits: the
blocks' requests of type `ty` are a prefix of the bytes of the queue followed by the submissions, and the storage the
history leaves represents a queue holding exactly the rest. -/
theorem history_delivery (L : Linked c ty) (h : KeptHistory cfg start blocks stop)
    (code : start.state.getCode c.address = c.code) {st : QueueState c.Record}
    (rep : Holds c (start.state.getStor c.address) st)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : History.NoSender systemAddress blocks) (authorities : History.NoAuthority systemAddress blocks)
    (creates : History.NoCreate systemAddress blocks) (data : History.DataWords blocks)
    (slots : queueBase c.width (st.tail + (History.submitted c blocks).length) ≤ 2 ^ 256)
    (count : st.count + (History.submitted c blocks).length < 2 ^ 256) :
    delivered ty blocks <+: (st.queue ++ History.submitted c blocks).flatMap c.out ∧
      ∃ k, ∃ st' : QueueState c.Record, Holds c (stop.state.getStor c.address) st' ∧
        st'.queue = (st.queue ++ History.submitted c blocks).drop k ∧
        delivered ty blocks = ((st.queue ++ History.submitted c blocks).take k).flatMap c.out := by
  obtain ⟨frames, chain, corr, out⟩ := history_chain L h code empty senders authorities creates data
  have hsub : Delivery.submissions frames = History.submitted c blocks := corr.submissions
  have d := chain.delivered rep (by rw [hsub]; exact slots) (by rw [hsub]; exact count)
  have queue := d.queue
  have output := d.output
  rw [hsub] at queue output
  rw [out] at output
  rw [output]
  exact ⟨take_flatMap_prefix _ _ _, _, _, d.represents, queue, rfl⟩

end History

/-! ## A reverted frame -/

/-- **A submission under a reverted parent is never delivered.** Whatever ran under a child whose settlement does not
commit, among it any submission at the contract: the run keeps at the contract what its continuation keeps, so it
submits what its continuation submits. -/
theorem reverted_never_delivered (c : Contract) {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {frame : Jaune.Frame}
    {resume : Resume} {childEvm : Evm} {raw out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc') (enter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post) (next : Exec pc' sevm post out)
    (rolled : ¬ Frame.settlementCommits frame raw = true) :
    Exec.keptAt c.address (.runOk step enter child resumed next) = Exec.keptAt c.address next ∧
      (Exec.keptAt c.address (.runOk step enter child resumed next)).filterMap (submittedBy c) =
        (Exec.keptAt c.address next).filterMap (submittedBy c) := by
  have same : Exec.keptAt c.address (.runOk step enter child resumed next) = Exec.keptAt c.address next := by
    rw [Exec.keptAt, dite_eq_right rolled, List.nil_append]
  exact ⟨same, by rw [same]⟩

end Blanc.Lift.BuilderRequest.ChainLink
