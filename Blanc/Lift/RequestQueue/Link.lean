import Batteries.Tactic.OpenPrivate
import Blanc.ExecutionKeptChain
import Blanc.SystemCallForward
import Blanc.Lift.RequestQueue.Chain

/-!
# From a chain's history to a request queue's steps, on the covered forks

`RequestQueue.Chain` takes a list of steps at a request contract as its input. This module produces that list
from a kept history whose blocks are all at covered forks (Prague onward, before Amsterdam): the frames the history
keeps at the contract, in order, one step each. A contract supplies, in `Linked`, a step for each kept user frame and
for its request-phase system call; the request phase's call at the contract is exactly one kept root, with the system
caller (`covered_request_root`).

* `history_chain`: the kept frames are a `Chain` of steps from the storage the history found to the storage it left,
  the steps push exactly what the contract's `record?` reads off the kept frames, their output is the blocks'
  requests of the contract's type, and each block's requests of that type are whole records.
* `chunks_flatMap`: whole records of one length cut back into the records.

The SYSTEM_ADDRESS exclusion (no frame with the system caller ran inside a user transaction) is discharged here from
the history's own premises: no code at SYSTEM_ADDRESS at the start, and no sender, authority or creation at it.

Retention only: no statement names a gas amount, a settlement amount or a frame that did not commit.
-/

namespace Blanc.Lift.RequestQueue.Link

open Jaune ExecutionTrace

open private runFrame_cases from Blanc.ExecutionKeptTop
open private withdrawalsPass_getCode withdrawalsPass_requests from Blanc.ExecutionKeptChain

/-! ## What a contract brings -/

/-- What the chain link needs of a request contract on the covered forks: where it sits, its request type, and a
queue step for each frame kept at it. `record?` reads the record a kept frame submits, if any. -/
structure Linked (q : Queue) where
  /-- The contract's address. -/
  address : Adr
  /-- Its runtime. -/
  code : ByteArray
  /-- Its request type byte. -/
  ty : UInt8
  /-- It is a canonical system contract, so its system call is the covered forks' envelope. -/
  member : (address, code) ∈ systemContracts
  /-- The code runs: it is nonempty and no delegation. -/
  runnable : code.toList ≠ [] ∧ ¬ isValidDelegation code
  /-- It is not the beacon-roots contract. -/
  beacon : beaconRootsAddress ≠ address
  /-- It is not the history contract. -/
  history : historyStorageAddress ≠ address
  /-- The type byte is not the deposit log's. -/
  ty_ne : ty ≠ 0
  /-- Prague's list holds the address exactly once, with this type byte, and nothing else with it. -/
  listed : pragueRequests.filter (fun p => p.1 == ty || p.2 == address) = [(ty, address)]
  /-- The record a kept frame submits. -/
  record? : Exec.Frame → Option q.Record
  /-- A frame with the system caller submits none. -/
  system_none : ∀ f : Exec.Frame, f.sevm.caller = systemAddress → record? f = none
  /-- A kept user frame is a step: on the storage it found and left, pushing its record, with no output. -/
  user : ∀ {f : Exec.Frame} {stat : BenvStat}, Exec.Frame.EntryIn address code stat f → CoveredFork stat.fork →
    f.sevm.caller ≠ systemAddress → ∃ s : Step q, s.before = Devm.getStor f.pre address ∧
      s.after = Devm.getStor f.post address ∧ pushed [s.effect] = (record? f).toList ∧ s.output = []
  /-- The request phase's call is a step: on the storage it found and left, pushing nothing, returning its output,
  which is whole records. -/
  system : ∀ {benv : Benv} {post : State} {out : MsgCallOutput}, CoveredFork benv.stat.fork →
    benv.state.getCode address = code → processCheckedSystemTransaction benv address [] = .ok (post, out) →
    ∃ s : Step q, s.before = benv.state.getStor address ∧ s.after = post.getStor address ∧
      pushed [s.effect] = [] ∧ s.output = out.returnData ∧ ∃ rs : List q.Record, out.returnData = rs.flatMap q.out

variable {q : Queue}

/-- Every covered fork lists Prague's request contracts. -/
theorem covered_requests {f : Fork} (h : CoveredFork f) : f.ruleSet.requests = pragueRequests :=
  h.cases (motive := fun f => f.ruleSet.requests = pragueRequests) rfl rfl rfl rfl

/-! ## Observers -/

/-- The bytes of one request entry after its type byte, if that byte is `ty`. -/
def entryOf (ty : UInt8) : Bytes → Option Bytes
  | [] => none
  | t :: tail => if t = ty then some tail else none

/-- The bytes of type `ty` in one block's requests. -/
def blockDelivered (ty : UInt8) (b : KeptBlock) : Bytes := (b.output.requests.filterMap (entryOf ty)).flatten

/-- The bytes of type `ty` a history's blocks output, in order. -/
def delivered (ty : UInt8) (blocks : List KeptBlock) : Bytes := blocks.flatMap (blockDelivered ty)

/-- The frames a history keeps at `a`, in order. -/
def kept (a : Adr) (blocks : List KeptBlock) : List Exec.Frame := blocks.flatMap (KeptBlock.keptAt a)

/-- What a request step at `a` returns, and nothing for a step elsewhere. -/
def stepOutput (a : Adr) (s : RequestStep) : Bytes := if s.target = a then s.output.returnData else []

/-- Bytes cut into pieces of `n` from the front; a short tail is kept as the last piece. -/
def chunks (n : Nat) (bytes : Bytes) : List Bytes :=
  (List.range ((bytes.length + (n - 1)) / n)).map fun i => (bytes.drop (n * i)).take n

/-- **Whole records cut back into the records.** -/
theorem chunks_flatMap {α : Type} (n : Nat) (out : α → Bytes) (len : ∀ r, (out r).length = n) (pos : 0 < n)
    (rs : List α) : chunks n (rs.flatMap out) = rs.map out := by
  induction rs with
  | nil =>
      simp only [chunks, List.flatMap_nil, List.length_nil, Nat.zero_add, List.map_nil]
      rw [Nat.div_eq_of_lt (by omega), List.range_zero, List.map_nil]
  | cons r rs ih =>
      unfold chunks at ih ⊢
      rw [List.flatMap_cons, List.map_cons, List.length_append, len r]
      have hl : ((rs.flatMap out).length + (n - 1)) / n = rs.length := by
        have := congrArg List.length ih
        rwa [List.length_map, List.length_range, List.length_map] at this
      have hs : (n + (rs.flatMap out).length + (n - 1)) / n = ((rs.flatMap out).length + (n - 1)) / n + 1 := by
        rw [show n + (rs.flatMap out).length + (n - 1) = ((rs.flatMap out).length + (n - 1)) + n * 1 by omega,
          Nat.add_mul_div_left _ _ pos]
      rw [hs, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · rw [Nat.mul_zero, List.drop_zero, List.take_left' (len r)]
      · rw [← ih]
        congr 1
        funext i
        simp only [Function.comp, Nat.mul_succ]
        rw [Nat.add_comm (n * i) n, ← List.drop_drop, List.drop_left' (len r)]

/-! ## The correspondence -/

/-- A step is this kept frame: the same storage before and after, the record it pushes is the one the frame
submits, and its output is whole records. -/
structure Matches (L : Linked q) (s : Step q) (f : Exec.Frame) : Prop where
  before : s.before = Devm.getStor f.pre L.address
  after : s.after = Devm.getStor f.post L.address
  pushes : pushed [s.effect] = (L.record? f).toList
  records : ∃ rs : List q.Record, s.output = rs.flatMap q.out

/-- The steps are the kept frames, one for one, in order. -/
def Corresponds (L : Linked q) (steps : List (Step q)) (kept : List Exec.Frame) : Prop :=
  List.Forall₂ (Matches L) steps kept

variable {L : Linked q}

theorem Corresponds.chain {steps : List (Step q)} {kept : List Exec.Frame} (h : Corresponds L steps kept)
    {s t : Stor} (chain : KeptChain L.address s kept t) : Chain s steps t := by
  induction h generalizing s with
  | nil =>
      cases chain
      exact .nil _
  | cons m _ ih =>
      cases chain with
      | cons starts tail => exact .cons (m.before.trans starts) (m.after ▸ ih tail)

/-- **The steps push what the kept frames submit.** -/
theorem Corresponds.submissions {steps : List (Step q)} {kept : List Exec.Frame} (h : Corresponds L steps kept) :
    RequestQueue.submissions steps = kept.filterMap L.record? := by
  induction h with
  | nil => rfl
  | @cons s f ss fs m _ ih =>
      change pushed ([s.effect] ++ effects ss) = _
      rw [pushed_append, m.pushes]
      change _ ++ RequestQueue.submissions ss = _
      rw [ih, List.filterMap_cons]
      cases L.record? f <;> rfl

/-- The kept frames have steps, with this output. -/
def Mapped (L : Linked q) (kept : List Exec.Frame) (out : Bytes) : Prop :=
  ∃ steps, Corresponds L steps kept ∧ RequestQueue.output steps = out

theorem Mapped.nil : Mapped L [] [] := ⟨[], .nil, rfl⟩

theorem Mapped.append {xs ys : List Exec.Frame} {o p : Bytes} (first : Mapped L xs o) (second : Mapped L ys p) :
    Mapped L (xs ++ ys) (o ++ p) := by
  obtain ⟨gs, h, rfl⟩ := first
  obtain ⟨hs, k, rfl⟩ := second
  refine ⟨gs ++ hs, ?_, by simp only [RequestQueue.output, List.flatMap_append]⟩
  induction h with
  | nil => exact k
  | cons m _ ih => exact .cons m ih

/-- A mapped output is whole records. -/
theorem Mapped.records {kept : List Exec.Frame} {out : Bytes} (h : Mapped L kept out) :
    ∃ rs : List q.Record, out = rs.flatMap q.out := by
  obtain ⟨steps, corr, rfl⟩ := h
  induction corr with
  | nil => exact ⟨[], rfl⟩
  | @cons s f ss fs m _ ih =>
      obtain ⟨rs, hr⟩ := m.records
      obtain ⟨rs', hr'⟩ := ih
      refine ⟨rs ++ rs', ?_⟩
      change s.output ++ RequestQueue.output ss = _
      rw [hr, hr', List.flatMap_append]

/-! ## User frames -/

/-- Kept frames with a caller other than the system have steps with no output. -/
theorem Mapped.ofUsers {kept : List Exec.Frame} {stat : BenvStat}
    (entries : ∀ f ∈ kept, Exec.Frame.EntryIn L.address L.code stat f) (fork : CoveredFork stat.fork)
    (callers : ∀ f ∈ kept, f.sevm.caller ≠ systemAddress) : Mapped L kept [] := by
  induction kept with
  | nil => exact .nil
  | cons f rest ih =>
      obtain ⟨s, before, after, pushes, out⟩ := L.user (entries f List.mem_cons_self) fork
        (callers f List.mem_cons_self)
      obtain ⟨ss, h, hout⟩ := ih (fun x hx => entries x (List.mem_cons_of_mem _ hx))
        (fun x hx => callers x (List.mem_cons_of_mem _ hx))
      refine ⟨s :: ss, .cons ⟨before, after, pushes, ⟨[], by rw [out]; rfl⟩⟩ h, ?_⟩
      change s.output ++ RequestQueue.output ss = []
      rw [out, hout]
      rfl

/-! ## The request step -/

theorem keptChain_nil {a : Adr} {s t : Stor} (h : KeptChain a s [] t) : s = t := by
  cases h
  rfl

/-- **A covered-fork request step at a system contract is exactly one kept root.** The checked system call runs one
root, on the legacy lane: the contract's code is no delegation and no precompile sits at its address; the root
commits, since the checked call had no error, and it is all the call keeps there. -/
theorem covered_request_root {benv : Benv} {a : Adr} {C : ByteArray} {post : State} {out : MsgCallOutput}
    {rs : List Root} (fork : CoveredFork benv.stat.fork) (member : (a, C) ∈ systemContracts)
    (installed : benv.state.getCode a = C) (runnable : C.toList ≠ [] ∧ ¬ isValidDelegation C)
    (run : processCheckedSystemTransaction benv a [] = .ok (post, out))
    (roots : MessageRoots (systemTransactionMessage benv a []) post out rs) :
    ∃ f, rs.flatMap (Root.keptAt a) = [f] ∧ f.sevm.caller = systemAddress ∧ f.sevm.data = [] ∧
      Devm.getStor f.pre a = benv.state.getStor a ∧ Devm.getStor f.post a = post.getStor a := by
  obtain ⟨noError, -⟩ := exists_systemRoots run
  have hsg : (systemTransactionMessage benv a []).benv.stat.rules.stateGas = none :=
    fork.rules_stateGas_none
  have hcode : (systemTransactionMessage benv a []).code = C := installed
  have hnd : getDelegatedCodeAddress C = none := systemContracts_nondelegated member
  have hdel : messageCallDelegation (systemTransactionMessage benv a []) =
      .ok (systemTransactionMessage benv a [], 0) := by
    unfold messageCallDelegation processMessageCall.legacyAuthorization
    have hauths : (systemTransactionMessage benv a []).tenv.stat.auths = [] := rfl
    simp only [hauths, List.isEmpty_nil, Bool.or_true, ↓reduceIte]
  have hres : messageCallExecutionMessage (systemTransactionMessage benv a []) = systemTransactionMessage benv a [] := by
    unfold messageCallExecutionMessage Msg.resolveCodeDelegation
    have hnone : (systemTransactionMessage benv a []).benv.stat.rules.delegatedCodeAddress
        (systemTransactionMessage benv a []).code = none := by
      simp only [ForkRules.delegatedCodeAddress, hcode, hnd, ite_self]
    rw [hnone]
  have hm := roots.1
  unfold processMessageCall at hm
  simp only [show (systemTransactionMessage benv a []).target.isNone = false from rfl, Bool.false_eq_true,
    ↓reduceIte] at hm
  unfold processMessageCall.call at hm
  rw [hsg] at hm
  dsimp only at hm
  obtain ⟨⟨d, refund⟩, hd, body⟩ := Except.bind_eq_ok hm
  have hd' : messageCallDelegation (systemTransactionMessage benv a []) = .ok (d, refund) := hd
  rw [hdel] at hd'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hd')
  obtain ⟨evm, hevm, tail⟩ := Except.bind_eq_ok body
  have core : processMessage (messageCallExecutionMessage (systemTransactionMessage benv a [])) = .ok evm :=
    Except.bimap_id_eq_ok hevm
  rw [hres] at core
  have herr : out.error = evm.error := by
    split at tail
    · obtain ⟨_, _, output⟩ := Except.bind_eq_ok tail
      rw [← (Prod.mk.inj (Except.ok.inj output)).2]
    · rw [← (Prod.mk.inj (Except.ok.inj tail)).2]
  have hentry : messageEntry (systemTransactionMessage benv a []) =
      enteredFrame (Frame.ofCall (systemTransactionMessage benv a [])) := by
    unfold messageEntry legacyEntry
    rw [hsg]
    dsimp only
    rw [hdel]
    simp only [show (systemTransactionMessage benv a []).target.isNone = false from rfl, Bool.false_eq_true,
      ↓reduceIte]
    rw [hres]
  have notPrecompile : ¬ benv.stat.rules.isPrecomp a := systemContracts_not_precompile member fork
  obtain ⟨benv', ht, cases⟩ := runFrame_cases (f := Frame.ofCall (systemTransactionMessage benv a [])) core
  have hb : benv' = benv.beginTransaction := (Except.ok.inj ht).symm
  subst hb
  rcases cases with ⟨-, adr, -, hca, hp⟩ | ⟨hsome, hs⟩
  · obtain rfl : a = adr := Option.some.inj hca
    have hp' : (!false && decide (benv.stat.rules.isPrecomp a)) = true := hp
    rw [decide_eq_false notPrecompile] at hp'
    exact absurd hp' (by decide)
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
          rw [← herr, noError]
          rfl
        obtain ⟨hcaller, here, -, hdata⟩ := roots.entry_routing mem
        have keep : Root.keptAt a r =
            [Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits settles)] := by
          rw [Root.keptAt, dite_eq_left settles, ite_eq_left (show r.evm.sta.currentTarget = a from here)]
        have flat : [r].flatMap (Root.keptAt a) =
            [Exec.Frame.ofRun r.run (Frame.raw_commits_of_settlementCommits settles)] := by
          rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, keep]
        have hc : (benv.state.getCode a).toList ≠ [] := by rw [installed]; exact runnable.1
        have hdl : ¬ isValidDelegation (benv.state.getCode a) := by rw [installed]; exact runnable.2
        refine ⟨_, flat, hcaller, hdata, (roots.entry_kept mem hc hdl).2, ?_⟩
        have chain := (roots.chain (a := a) hc hdl).1
        rw [flat] at chain
        cases chain with
        | cons starts rest => exact keptChain_nil rest

/-- A request step at the contract is one kept root, and the contract's system step, with the output it returned. -/
theorem Mapped.ofRequestStep {benv : Benv} {post : State} {out : MsgCallOutput} {rs : List Root}
    (fork : CoveredFork benv.stat.fork) (code : benv.state.getCode L.address = L.code)
    (run : processCheckedSystemTransaction benv L.address [] = .ok (post, out))
    (roots : MessageRoots (systemTransactionMessage benv L.address []) post out rs) :
    Mapped L (rs.flatMap (Root.keptAt L.address)) out.returnData := by
  obtain ⟨f, flat, caller, -, before, after⟩ := covered_request_root fork L.member code L.runnable run roots
  obtain ⟨s, sb, sa, pushes, sout, records⟩ := L.system fork code run
  rw [flat]
  refine ⟨[s], .cons ⟨sb.trans before.symm, sa.trans after.symm, ?_, ?_⟩ .nil, ?_⟩
  · rw [pushes, L.system_none f caller]
    rfl
  · rw [sout]
    exact records
  · change s.output ++ [] = _
    rw [sout, List.append_nil]

/-- **The request fold, as steps.** The step at the contract is its system step; a step elsewhere keeps only user
frames there. -/
theorem Mapped.ofRequestRoots {idx : Nat} {contracts : List (UInt8 × Adr)} {benv : Benv}
    {acc acc' : List Bytes} {bal bal' : BalBuilder} {final : State} {steps : List RequestStep}
    (h : RequestRoots idx contracts benv acc bal final acc' bal' steps) (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode L.address = L.code)
    (others : ∀ s ∈ steps, s.target ≠ L.address → ∀ f ∈ s.roots.flatMap (Root.keptAt L.address),
      f.sevm.caller ≠ systemAddress)
    (entries : ∀ f ∈ (requestRootsOf steps).flatMap (Root.keptAt L.address),
      Exec.Frame.EntryIn L.address L.code benv.stat f) :
    Mapped L ((requestRootsOf steps).flatMap (Root.keptAt L.address)) (steps.flatMap (stepOutput L.address)) := by
  obtain ⟨hc, hd⟩ := L.runnable
  induction h with
  | nil benv acc bal => exact .nil
  | @cons type target rest benv acc acc' bal bal' post final out rs steps hcall roots tail ih =>
      have split : (requestRootsOf (⟨type, target, post, out, rs⟩ :: steps)).flatMap (Root.keptAt L.address) =
          rs.flatMap (Root.keptAt L.address) ++ (requestRootsOf steps).flatMap (Root.keptAt L.address) := by
        unfold requestRootsOf
        rw [List.flatMap_cons, List.flatMap_append]
      have hc' : (benv.state.getCode L.address).toList ≠ [] := by rw [code]; exact hc
      have hd' : ¬ isValidDelegation (benv.state.getCode L.address) := by rw [code]; exact hd
      have code' : post.getCode L.address = benv.state.getCode L.address := (MessageRoots.chain roots hc' hd').2
      rw [split] at entries ⊢
      rw [List.flatMap_cons]
      have below := ih fork (code'.trans code)
        (fun s hs => others s (List.mem_cons_of_mem _ hs))
        (fun f hf => entries f (List.mem_append_right _ hf))
      refine Mapped.append ?_ below
      by_cases here : target = L.address
      · subst here
        have same : stepOutput L.address ⟨type, L.address, post, out, rs⟩ = out.returnData := ite_eq_left rfl
        rw [same]
        exact Mapped.ofRequestStep fork code hcall roots
      · have same : stepOutput L.address ⟨type, target, post, out, rs⟩ = [] := ite_eq_right here
        rw [same]
        exact Mapped.ofUsers (fun f hf => entries f (List.mem_append_left _ hf)) fork
          (others _ List.mem_cons_self here)

/-! ## The request bytes -/

theorem steps_entries {ty : UInt8} {a : Adr} {steps : List RequestStep}
    (typed : ∀ s ∈ steps, s.type = ty ↔ s.target = a) :
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

/-- Under a covered fork a request's type is the contract's exactly when its target is. -/
theorem Linked.typed (L : Linked q) {f : Fork} (fork : CoveredFork f) (p : UInt8 × Adr)
    (hp : p ∈ f.ruleSet.requests) : p.1 = L.ty ↔ p.2 = L.address := by
  rw [covered_requests fork] at hp
  have key : (p.1 = L.ty ∨ p.2 = L.address) → p = (L.ty, L.address) := by
    intro either
    have mem : p ∈ pragueRequests.filter (fun p => p.1 == L.ty || p.2 == L.address) :=
      List.mem_filter.mpr ⟨hp, by simp only [Bool.or_eq_true, beq_iff_eq]; exact either⟩
    rw [L.listed] at mem
    exact List.mem_singleton.mp mem
  exact ⟨fun e => by rw [key (.inl e)], fun e => by rw [key (.inr e)]⟩

section Body

variable {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal} {state : State}
  {bout : BlockOutput} {run : BodyRun}

/-- **A block's requests of the contract's type are what the request steps at the contract returned.** The deposit
log's entry has type byte 0, which is not the contract's. -/
theorem block_entries (L : Linked q) (h : BodyRoots benv txs ommers wds state bout run)
    (fork : CoveredFork benv.stat.fork) :
    (bout.requests.filterMap (entryOf L.ty)).flatten = run.requests.flatMap (stepOutput L.address) := by
  by_cases on : benv.stat.rules.header.requestsHash = true
  · obtain ⟨deposits, -, eq⟩ := h.requests_eq on
    have typed : ∀ s ∈ run.requests, s.type = L.ty ↔ s.target = L.address := fun s hs =>
      L.typed fork (s.type, s.target) (by
        have := h.contracts_eq on
        change benv.stat.fork.ruleSet.requests = _ at this
        rw [this]
        exact List.mem_map_of_mem hs)
    rw [eq, List.filterMap_append, List.flatten_append, steps_entries typed]
    have zero : ¬ (0 : UInt8) = L.ty := fun same => L.ty_ne same.symm
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

/-- **A body's kept frames at the contract, as steps.** Outside the request fold they are user frames; the fold is
`Mapped.ofRequestRoots`. -/
theorem Mapped.ofBody (h : BodyRoots benv txs ommers wds state bout run)
    (rules : KeptRules benv.stat.rules) (fork : CoveredFork benv.stat.fork)
    (code : benv.state.getCode L.address = L.code) (created : L.address ∉ benv.createdAccounts)
    (outside : ∀ f ∈ run.outsideRequests L.address, f.sevm.caller ≠ systemAddress)
    (others : ∀ s ∈ run.requests, s.target ≠ L.address → ∀ f ∈ s.roots.flatMap (Root.keptAt L.address),
      f.sevm.caller ≠ systemAddress)
    (entries : ∀ f ∈ run.roots.flatMap (Root.keptAt L.address), Exec.Frame.EntryIn L.address L.code benv.stat f) :
    Mapped L (run.roots.flatMap (Root.keptAt L.address)) (run.requests.flatMap (stepOutput L.address)) := by
  have split : run.roots.flatMap (Root.keptAt L.address) = run.outsideRequests L.address ++
      (requestRootsOf run.requests).flatMap (Root.keptAt L.address) := by
    unfold BodyRun.roots BodyRun.outsideRequests
    rw [List.flatMap_append]
  rw [split] at entries ⊢
  have first : Mapped L (run.outsideRequests L.address) [] :=
    Mapped.ofUsers (fun f hf => entries f (List.mem_append_left _ hf)) fork outside
  have second : Mapped L ((requestRootsOf run.requests).flatMap (Root.keptAt L.address))
      (run.requests.flatMap (stepOutput L.address)) := by
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
      obtain ⟨hne, hnd⟩ := L.runnable
      have hc : (benv.state.getCode L.address).toList ≠ [] := by rw [code]; exact hne
      have hd : ¬ isValidDelegation (benv.state.getCode L.address) := by rw [code]; exact hnd
      have code₁ := (h.pre.chain hc hd).2
      have code₂ := (roots.chain rules (a := L.address) (by simpa only [Benv.withState, code₁] using hc)
        (by simpa only [Benv.withState, code₁] using hd) created).2
      refine Mapped.ofRequestRoots fold ?_
        ((withdrawalsPass_getCode _ _ _ _ L.address).trans (code₂.trans (code₁.trans code))) others ?_
      · change CoveredFork run.txEnv.stat.fork
        rw [hs]
        exact fork
      · intro f hf
        change Exec.Frame.EntryIn L.address L.code run.txEnv.stat f
        rw [hs]
        exact entries f (List.mem_append_right _ hf)
    · rw [h.requests_off on]
      exact .nil
  exact first.append second

end Body

/-! ## The history -/

section History

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- The history's kept frames at the contract have steps, whose output is the blocks' requests of its type, and each
block's requests of that type are whole records. -/
theorem Mapped.ofHistory (h : KeptHistory cfg start blocks stop) (covered : ∀ b ∈ blocks, CoveredFork b.fork)
    (code : start.state.getCode L.address = L.code)
    (outside : ∀ b ∈ blocks, ∀ f ∈ b.run.outsideRequests L.address, f.sevm.caller ≠ systemAddress)
    (others : ∀ b ∈ blocks, ∀ s ∈ b.run.requests, s.target ≠ L.address →
      ∀ f ∈ s.roots.flatMap (Root.keptAt L.address), f.sevm.caller ≠ systemAddress)
    (entries : ∀ b ∈ blocks, ∀ f ∈ b.keptAt L.address, Exec.Frame.EntryIn L.address L.code b.benv.stat f) :
    Mapped L (kept L.address blocks) (delivered L.ty blocks) ∧
      ∀ b ∈ blocks, ∃ rs : List q.Record, blockDelivered L.ty b = rs.flatMap q.out := by
  obtain ⟨hne, hnd⟩ := L.runnable
  have hc : (start.state.getCode L.address).toList ≠ [] := by rw [code]; exact hne
  have hd : ¬ isValidDelegation (start.state.getCode L.address) := by rw [code]; exact hnd
  induction h with
  | refl => exact ⟨.nil, fun _ hb => absurd hb List.not_mem_nil⟩
  | @step blocks b post prior step ih =>
      have mem : b ∈ blocks ++ [b] := List.mem_append_right _ List.mem_cons_self
      obtain ⟨below, wholes⟩ := ih (fun x hx => covered x (List.mem_append_left _ hx))
        (fun x hx => outside x (List.mem_append_left _ hx))
        (fun x hx => others x (List.mem_append_left _ hx)) (fun x hx => entries x (List.mem_append_left _ hx))
      have one := Mapped.ofBody step.body step.kept.rules (covered b mem) ((prior.chain hc hd).2.trans code)
        AdrSet.not_mem_empty (outside b mem) (others b mem) (entries b mem)
      rw [← block_entries L step.body (covered b mem)] at one
      refine ⟨?_, fun x hx => ?_⟩
      · unfold kept delivered
        rw [List.flatMap_append, List.flatMap_append, List.flatMap_singleton, List.flatMap_singleton]
        exact below.append one
      · rcases List.mem_append.mp hx with hx | hx
        · exact wholes x hx
        · rw [List.mem_singleton.mp hx]
          exact one.records

/-- **The proof-level form.** On a history at covered forks, from the contract's code at the start, no code at
SYSTEM_ADDRESS, and no sender, authority or creation at it: the frames the history keeps at the contract are a chain
of steps, one for one, from the storage the history found to the storage it left; the steps push what `record?` reads
off the kept frames; their output is the blocks' requests of the contract's type; and each block's requests of that
type are whole records. -/
theorem history_chain (L : Linked q) (h : KeptHistory cfg start blocks stop)
    (covered : ∀ b ∈ blocks, CoveredFork b.fork) (code : start.state.getCode L.address = L.code)
    (empty : start.state.getCode systemAddress = ByteArray.empty)
    (senders : ∀ b ∈ blocks, NoSenderAt systemAddress b.run.senders)
    (authorities : ∀ b ∈ blocks, NoAuthorityAt systemAddress b.run.senders)
    (creates : ∀ b ∈ blocks, NoCreateAt systemAddress b.run.roots) :
    ∃ steps, Chain (start.state.getStor L.address) steps (stop.state.getStor L.address) ∧
      RequestQueue.submissions steps = (kept L.address blocks).filterMap L.record? ∧
      RequestQueue.output steps = delivered L.ty blocks ∧
      ∀ b ∈ blocks, ∃ rs : List q.Record, blockDelivered L.ty b = rs.flatMap q.out := by
  obtain ⟨hne, hnd⟩ := L.runnable
  have hc : (start.state.getCode L.address).toList ≠ [] := by rw [code]; exact hne
  have hd : ¬ isValidDelegation (start.state.getCode L.address) := by rw [code]; exact hnd
  obtain ⟨outside, others, -⟩ := h.caller_ne (a := L.address) empty L.beacon L.history senders authorities creates
  obtain ⟨⟨steps, corr, out⟩, wholes⟩ := Mapped.ofHistory h covered code outside others
    (h.entry_in code hne hnd)
  exact ⟨steps, corr.chain (h.chain hc hd).1, corr.submissions, out, wholes⟩

end History

end Blanc.Lift.RequestQueue.Link
