import Blanc.Lift.BuilderRequest.SystemOutput

/-!
# The builder contracts' calldata latch, under Amsterdam

A system call with nonempty calldata runs the same drain as one with empty calldata; at the excess update
the bytes branch on `CALLDATASIZE` before reading slot 0, store the inhibitor there, clear the count and
return. So `latch` differs from the empty-calldata call only in slot 0.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestSystem

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

/-- The excess update on nonempty calldata: no read, store the inhibitor. -/
theorem latch_run (p : LatchWords) {fs : List SFunc} {sevm : Sevm} {d : Devm} {c : B256} {M : Mem}
    {G : Nat} {oc : Outcome} (hdata : sevm.data.length.toB256 ≠ 0)
    (next : SFunc.RunExact fs sevm (St d [B256.max, c] M G) (sysFinal p.len) oc) :
    SFunc.RunExact fs sevm (St d [c] M (G + 20)) (sysExcess p) oc := by
  have e : G + 20 = G + 3 + 1 + 10 + 3 + 2 + 1 := by omega
  rw [e]
  unfold sysExcess sysLatch
  refine rx_dest ?_
  refine rx_calldatasize (by rroom) ?_
  refine rx_push rfl (by rroom) ?_
  refine rx_branch_succ hdata ?_
  refine rx_dest ?_
  refine rx_push inhibitor_push (by rroom) ?_
  exact next

variable (k : SysPath)

section Frame

variable (sevm : Sevm) (b : Devm)

/-- The frame's exact charge on nonempty calldata. -/
def latchCost : Nat :=
  chargedRetExt (k.drain sevm b).memory 0 (k.outLen sevm b) +
    finalGas sevm (k.booked sevm b) B256.max + 20 +
    bookGas sevm (k.drain sevm b).base (SysPath.rd sevm b 2) (k.count sevm b) (SysPath.rd sevm b 3) +
    (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b + dispatchGas

/-- The frame's post state on nonempty calldata, at `G` of remaining gas. -/
def latchPost (G : Nat) : Devm :=
  chargedRetPost (finalBase sevm (k.booked sevm b) B256.max) [] (k.drain sevm b).memory G 0
    (k.outLen sevm b)

variable {sevm b}

/-- **The whole system frame on nonempty calldata**, from any storage. `tree` and `len` say the runtime's
excess update is the builder arm. -/
theorem latch_frame_run (p : LatchWords) (tree : k.shape.excessTree = sysExcess p)
    (len : p.len = k.shape.len) (hfork : sevm.benvStat.fork = .amsterdam)
    (hstatic : sevm.isStatic = false) (hcaller : sevm.caller = systemAddress)
    (hdata : sevm.data.length.toB256 ≠ 0)
    (r : Ready sevm b [2, 3, 0, 1]) {G : Nat} (hG : gCallStipend < G) :
    SFunc.RunExact k.cert.prog sevm (St b [] .empty (G + latchCost k sevm b))
      (dispatchTree k.systemDest k.user (sysSetup k.shape k.body)) (.halted (latchPost k sevm b G)) := by
  have hsg := amsterdam_stateGas (s := sevm.benvStat) hfork
  have hpush0 := amsterdam_push0 (s := sevm.benvStat) hfork
  have rSetup : Ready sevm (setupBase sevm b) [2, 3, 0, 1] := (r.sload 3).sload 2
  have rDrain := k.fold_ready (h := SysPath.rd sevm b 2) 0 (k.count sevm b).toNat (M := .empty) rSetup
  have rBooked := ready_book rDrain (SysPath.rd sevm b 2) (k.count sevm b) (SysPath.rd sevm b 3)
  have s1 := final_run k.shape.len (fs := k.cert.prog) (d := k.booked sevm b)
    (e := B256.max) (c := k.count sevm b) (M := (k.drain sevm b).memory) hsg hpush0
    hstatic hG rBooked (by decide)
  have s2 := latch_run p (fs := k.cert.prog) hdata (by rw [len]; exact s1)
  rw [← tree] at s2
  have s3 := k.frame_prefix hfork hstatic hcaller r (by omega) s2
  have e : G + latchCost k sevm b =
      G + chargedRetExt (k.drain sevm b).memory 0 (k.outLen sevm b) +
        finalGas sevm (k.booked sevm b) B256.max + 20 +
        bookGas sevm (k.drain sevm b).base (SysPath.rd sevm b 2) (k.count sevm b) (SysPath.rd sevm b 3) +
        (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b + dispatchGas := by
    simp only [latchCost]
    omega
  rw [e]
  exact s3

end Frame

/-! ## The post state -/

/-- The exact post state of a builder system call on nonempty calldata: the pointers as `sysState` moves
them, slot 0 at the inhibitor, the count cleared, nothing else. -/
def latchState (p : SysShape) (σ : State) (a : Adr) : State :=
  let rd : B256 → B256 := fun key => (σ.getStor a).get key
  let c := drainCount p.cap.word (rd 2) (rd 3)
  let σ1 := if rd 2 + c = rd 3 then (σ.setStorVal a 2 0).setStorVal a 3 0
    else σ.setStorVal a 2 (rd 2 + c)
  (σ1.setStorVal a 0 B256.max).setStorVal a 1 0

theorem latchPost_state (k : SysPath) (sevm : Sevm) (b : Devm) (G : Nat) :
    (latchPost k sevm b G).state = latchState k.shape b.state sevm.currentTarget := by
  show (finalBase sevm (k.booked sevm b) B256.max).state = _
  simp only [finalBase, afterSstoreA_state, SysPath.booked, SysPath.bookBase_state, SysPath.drain_state]
  rfl

/-- Slot by slot, the latch's post storage is the empty-calldata call's, except that slot 0 is the
inhibitor. -/
theorem latchState_get (p : SysShape) (σ : State) (a : Adr) (key : B256) :
    ((latchState p σ a).getStor a).get key =
      if (0 : B256) = key then B256.max else ((sysState p σ a).getStor a).get key := by
  simp only [latchState, sysState]
  split <;> simp only [State.getStor_setStorVal_self, Stor.get_set_ite] <;>
    by_cases h0 : (0 : B256) = key <;> by_cases h1 : (1 : B256) = key <;>
    simp only [h0, h1, ite_true, ite_false]
  all_goals
    exact absurd (h0.trans h1.symm) (by decide)

theorem latchState_bal (p : SysShape) (σ : State) (a x : Adr) :
    ((latchState p σ a).get x).bal = (σ.get x).bal := by
  simp only [latchState]
  split <;> simp only [bal_setStorVal]

theorem latchState_getCode (p : SysShape) (σ : State) (a x : Adr) :
    (latchState p σ a).getCode x = σ.getCode x := by
  simp only [latchState]
  split <;> simp only [State.getCode_setStorVal]

/-! ## The gas -/

section Gas

variable {k : SysPath}

/-- The latch stays within the rule-relative bound of the empty-calldata frame: calldata adds no memory
or storage, the arm reads nothing, and its two stores are priced as the empty-calldata path's bound prices
them, cold. -/
theorem latchCost_le (m : SysMemory k) (sevm : Sevm) (b : Devm) :
    latchCost k sevm b ≤ k.frameBound m.alloc := by
  have hp := SysPath.prefix_le m sevm b
  have c1 := sstoreCostA_le A sevm (k.booked sevm b) 0 B256.max
  have c2 := sstoreCostA_le A sevm (afterSstoreA A sevm (k.booked sevm b) 0 B256.max) 1 0
  simp only [latchCost, finalGas]
  omega

end Gas

/-! ## The envelope -/

section Envelope

variable {k : SysPath} {benv : Benv} {target : Adr} {data : Bytes}

/-- The post frame at the message's gas, on nonempty calldata. -/
abbrev latchCallPost (k : SysPath) (benv : Benv) (target : Adr) (data : Bytes) : Devm :=
  let s := initSevm (systemCallMsg benv target k.code data)
  let b := systemCallBase (systemCallMsg benv target k.code data)
  latchPost k s b (systemTransactionGas - latchCost k s b)

/-- **The checked system call on nonempty calldata**, from any storage, with its exact post state and a
regular-gas bound. State gas is excluded; see `RegularGasWithin`. -/
theorem latch_spec (c : SysCall k) (p : LatchWords) (tree : k.shape.excessTree = sysExcess p)
    (len : p.len = k.shape.len) (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode c.target = k.code) (hdata : data.length.toB256 ≠ 0) :
    processCheckedSystemTransaction benv c.target data =
      .ok (latchState k.shape benv.state c.target,
        systemCallOutputA (systemCallMsg benv c.target k.code data) (latchCallPost k benv c.target data)) ∧
    RegularGasWithin (latchCallPost k benv c.target data).gasLeft c.bound := by
  let s := initSevm (systemCallMsg benv c.target k.code data)
  let b := systemCallBase (systemCallMsg benv c.target k.code data)
  have hle := latchCost_le c.memory s b
  have hB := c.bound_le
  have hroom := c.room
  have r : Ready s b [2, 3, 0, 1] := SysPath.ready_base hfork
  have hG : gCallStipend < systemTransactionGas - latchCost k s b := by omega
  have run := latch_frame_run k p tree len (sevm := s) (b := b) hfork rfl rfl hdata r hG
  rw [show systemTransactionGas - latchCost k s b + latchCost k s b = systemTransactionGas by omega,
    show St b [] .empty systemTransactionGas = b from systemCallBase_St] at run
  have hexec : Nonempty (Exec 0 s b (.ok (latchPost k s b (systemTransactionGas - latchCost k s b)))) :=
    lift_exact_noExec k.check k.jumps rfl k.noExec ⟨_, k.root, run⟩
  have hrun := (exec_iff_exec_eq _ _ _ _).mp hexec
  have rSetup : Ready s (setupBase s b) [2, 3, 0, 1] := (r.sload 3).sload 2
  have rDrain := k.fold_ready (h := SysPath.rd s b 2) 0 (k.count s b).toNat (M := .empty) rSetup
  have rBooked := ready_book rDrain (SysPath.rd s b 2) (k.count s b) (SysPath.rd s b 3)
  have rEnd := (rBooked.sstore (by decide) B256.max).sstore (by decide) (0 : B256)
  have hcall := processCheckedSystemTransaction_amsterdam_of_exec hfork installed c.nonempty
    (SysPath.not_delegated_of_size c.size_ne) c.not_precompile hrun rEnd.error rEnd.refund
  rw [show (latchPost k s b (systemTransactionGas - latchCost k s b)).state =
    latchState k.shape benv.state c.target from latchPost_state _ _ _ _] at hcall
  refine ⟨hcall, ?_⟩
  show systemTransactionGas - latchCost k s b ≤ systemTransactionGas ∧
    systemTransactionGas - (systemTransactionGas - latchCost k s b) ≤ c.bound
  omega

theorem latchPost_output (k : SysPath) (sevm : Sevm) (b : Devm) (G G' : Nat) :
    (latchPost k sevm b G).output = (k.framePost sevm b G').output := by
  unfold latchPost SysPath.framePost
  rw [chargedRetPost_output, chargedRetPost_output]

/-- The latch returns what the empty-calldata call returns: the same records, read from the same
storage. -/
theorem latch_output {m : SysMemory k} (o : SysOutput k m) (benv : Benv) (target : Adr) (data : Bytes) :
    (latchCallPost k benv target data).output = (SysPath.callPost k benv target).output :=
  ((latchPost_output k _ _ _ 0).trans (o.framePost_output _ _ _)).trans (o.callPost_output benv target).symm

end Envelope

/-- Nonempty calldata is seen as nonempty by `CALLDATASIZE` when it has fewer than `2 ^ 256` bytes. -/
theorem data_length_ne {data : Bytes} (hne : data ≠ []) (hlen : data.length < 2 ^ 256) :
    data.length.toB256 ≠ 0 := by
  intro h
  have := congrArg B256.toNat h
  rw [B256.toNat_toB256_of_lt hlen] at this
  exact hne (List.eq_nil_of_length_eq_zero this)

/-- **The latch and what it leaves**, from any storage, for a runtime whose excess update is the builder
arm. -/
theorem latch_headline {k : SysPath} (c : SysCall k) {m : SysMemory k} (o : SysOutput k m)
    (p : LatchWords) (tree : k.shape.excessTree = sysExcess p) (len : p.len = k.shape.len)
    {benv : Benv} {data : Bytes} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode c.target = k.code) (hne : data ≠ []) (hlen : data.length < 2 ^ 256) :
    ∃ out emptyOut,
      processCheckedSystemTransaction benv c.target data =
        .ok (latchState k.shape benv.state c.target, out) ∧
      RegularGasWithin out.gasLeft c.bound ∧
      processCheckedSystemTransaction benv c.target [] =
        .ok (sysState k.shape benv.state c.target, emptyOut) ∧
      out.returnData = emptyOut.returnData := by
  obtain ⟨h1, g1⟩ := latch_spec c p tree len hfork installed (data_length_ne hne hlen)
  obtain ⟨h2, _⟩ := c.spec hfork installed
  exact ⟨_, _, h1, g1, h2, latch_output o _ _ _⟩

/-- Slot 0 after the latch holds the inhibitor, and slot 1 is cleared. -/
theorem latchState_slots (p : SysShape) (σ : State) (a : Adr) :
    ((latchState p σ a).getStor a).get 0 = B256.max ∧ ((latchState p σ a).getStor a).get 1 = 0 := by
  constructor
  · rw [latchState_get, ite_eq_left rfl]
  · rw [latchState_get, ite_eq_right (by decide), sysState_get]
    rfl

/-- After the latch, the next empty-calldata call moves slot 0 to the shape's next excess at the
inhibitor. -/
theorem sysState_latchState_zero (p : LatchWords) (s : SysShape) (hnext : s.next = excessNext p.target.word)
    (σ : State) (a : Adr) :
    ((sysState s (latchState s σ a) a).getStor a).get 0 = 0 := by
  rw [sysState_get_zero, hnext, (latchState_slots s σ a).1, excessNext_inhibitor]

/-- The empty-calldata call at any state holding the code. -/
theorem call_at {k : SysPath} (c : SysCall k) {benv : Benv} (hfork : benv.stat.fork = .amsterdam) (σ : State)
    (h : σ.getCode c.target = k.code) :
    ∃ out, processCheckedSystemTransaction (benv.withState σ) c.target [] =
        .ok (sysState k.shape σ c.target, out) ∧ RegularGasWithin out.gasLeft c.bound :=
  let hs := c.spec (benv := benv.withState σ) hfork h
  ⟨_, hs.1, hs.2⟩

/-- **The cycle.** The latch leaves slot 0 at the inhibitor, and the next empty-calldata call, at the state
the latch left, succeeds and moves slot 0 to 0. -/
theorem latch_cycle {k : SysPath} (c : SysCall k) (p : LatchWords)
    (tree : k.shape.excessTree = sysExcess p) (len : p.len = k.shape.len)
    (hnext : k.shape.next = excessNext p.target.word) {benv : Benv} {data : Bytes}
    (hfork : benv.stat.fork = .amsterdam) (installed : benv.state.getCode c.target = k.code)
    (hne : data ≠ []) (hlen : data.length < 2 ^ 256) :
    ∃ out out',
      processCheckedSystemTransaction benv c.target data =
        .ok (latchState k.shape benv.state c.target, out) ∧
      ((latchState k.shape benv.state c.target).getStor c.target).get 0 = B256.max ∧
      processCheckedSystemTransaction (benv.withState (latchState k.shape benv.state c.target)) c.target [] =
        .ok (sysState k.shape (latchState k.shape benv.state c.target) c.target, out') ∧
      RegularGasWithin out'.gasLeft c.bound ∧
      ((sysState k.shape (latchState k.shape benv.state c.target) c.target).getStor c.target).get 0 = 0 := by
  obtain ⟨h1, _⟩ := latch_spec c p tree len hfork installed (data_length_ne hne hlen)
  obtain ⟨_, h2, g2⟩ := call_at c hfork (latchState k.shape benv.state c.target)
    ((latchState_getCode _ _ _ _).trans installed)
  exact ⟨_, _, h1, (latchState_slots _ _ _).1, h2, g2, sysState_latchState_zero p _ hnext _ _⟩

/-- The checked system call at `a` on `data` returns, and no account's balance differs afterwards. -/
def KeepsBalances (benv : Benv) (a : Adr) (data : Bytes) : Prop :=
  ∃ post out, processCheckedSystemTransaction benv a data = .ok (post, out) ∧
    ∀ x, (post.get x).bal = (benv.state.get x).bal

/-- **A checked system call changes no balance**, from any storage, on either calldata form. -/
theorem keepsBalances {k : SysPath} (c : SysCall k) (p : LatchWords)
    (tree : k.shape.excessTree = sysExcess p) (len : p.len = k.shape.len) {benv : Benv} {data : Bytes}
    (hfork : benv.stat.fork = .amsterdam) (installed : benv.state.getCode c.target = k.code)
    (hlen : data.length < 2 ^ 256) : KeepsBalances benv c.target data := by
  by_cases hne : data = []
  · subst hne
    exact ⟨_, _, (c.spec hfork installed).1, sysState_bal _ _ _⟩
  · exact ⟨_, _, (latch_spec c p tree len hfork installed (data_length_ne hne hlen)).1,
      latchState_bal _ _ _⟩

/-- A storage that agrees with a represented one except at slot 0 represents the same queue, with slot 0's
value as its excess. -/
theorem Represents.of_slot0 {Record : Type} {width : Nat} {words : Record → Nat → B256}
    {f g : B256 → B256} {st : QueueState Record} (rep : Represents width words f st)
    (agree : ∀ key, (0 : B256) ≠ key → g key = f key) {v : Nat} (hv : v < 2 ^ 256)
    (h0 : g 0 = v.toB256) :
    Represents width words g { st with excess := v } where
  coherent := rep.coherent
  excess_lt := hv
  count_lt := rep.count_lt
  head_lt := rep.head_lt
  tail_lt := rep.tail_lt
  live_lt := rep.live_lt
  excess := h0
  count := (agree 1 (by decide)).trans rep.count
  head := (agree 2 (by decide)).trans rep.head
  tail := (agree 3 (by decide)).trans rep.tail
  live := fun i hi j hj =>
    (agree _ (queueSlot_ne (n := 0) (by omega) (by decide) (rep.live_lt i hi) hj)).trans (rep.live i hi j hj)

/-- On a represented queue, the latch's post storage represents the drained queue, with slot 0 at the
inhibitor. -/
theorem represents_latchState {Record : Type} {width : Nat} {words : Record → Nat → B256} (p : SysShape)
    {capN : Nat} (hcap : p.cap.word.toNat = capN) (hnext : p.next = excessNext p.target.word) {σ : State}
    {a : Adr} {st : QueueState Record} (rep : Represents width words (storOf σ a) st) :
    Represents width words (storOf (latchState p σ a) a)
      { drainedState capN p.target.word st with excess := 2 ^ 256 - 1 } :=
  (represents_sysState p hcap hnext rep).of_slot0
    (fun key hk => by
      show ((latchState p σ a).getStor a).get key = _
      rw [latchState_get, ite_eq_right hk])
    (by decide)
    ((latchState_slots p σ a).1.trans (by decide))

end Blanc.Lift.BuilderRequest
