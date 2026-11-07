import Blanc.Lift.RequestSystem.Path

/-!
# A request contract's system call, under Amsterdam: gas and the envelope

`SysPath.frameCost` is bounded against Jaune's `StateGasRules` record (`frameBound`), and the frame is
taken through `processCheckedSystemTransaction` with its exact post state. `SysMemory` is what a runtime
must add for this: its records' memory writes stay within a fixed allocation.

The `Ready` base is discharged from the real prepared base: the reservoir is the system grant
(`systemMaxSstoresPerCall × storageSet`), of which the frame's four stores need at most four units.
-/

namespace Blanc.Lift.RequestSystem

open Jaune

/-- Amsterdam's state-gas record. -/
local notation "A" => amsterdamStateGasRules

/-- A literal plus a word of known value, without wrap. -/
theorem lit_add_toNat {a x : B256} {n m : Nat} (ha : a.toNat = n) (hx : x.toNat = m)
    (h : n + m < 2 ^ 256) : (a + x).toNat = n + m := by
  rw [B256.toNat_add_eq_of_nof _ _ (by unfold B256.Nof; omega), ha, hx]

/-- A word product by a small number without wrap. -/
theorem mul_toB256_toNat_of_lt {a : B256} {n : Nat} (hn : n < 2 ^ 256) (h : a.toNat * n < 2 ^ 256) :
    (a * n.toB256).toNat = a.toNat * n := by
  rw [B256.toNat_mul, B256.toNat_toB256_of_lt hn]
  exact Nat.mod_eq_of_lt h

/-- A runtime's memory facts: every record's writes stay within a fixed aligned allocation. -/
structure SysMemory (k : SysPath) where
  /-- The allocation bound, in bytes. -/
  alloc : Nat
  aligned : alloc % 32 = 0
  /-- A returned record's length, as a number. -/
  lenN : Nat
  len_word : k.shape.len.word.toNat = lenN
  len_le : lenN * k.capN ≤ alloc
  /-- Every write of every record below the cap fits. -/
  windows : ∀ rd h (i : Nat), i < k.capN →
    ∀ w ∈ (k.stage rd h i.toB256).footprint, w.1 + w.2 ≤ alloc
  alloc_lt : alloc < 2 ^ 256

namespace SysPath

variable (k : SysPath)

/-- The rule-relative bound on a frame's charge. -/
def frameBound (alloc : Nat) : Nat :=
  k.capN * (23 + k.bodyFixed + k.slots * gasColdSload + gVerylow * k.writes) +
    calculateMemoryGasCost alloc + 249 + 4 * gasColdSload +
    4 * (gasColdSload + amsterdamStateGasRules.storageWrite)

variable {k}

/-- The loop's charges, with the memory's expansion left over. -/
theorem fold_charges (m : SysMemory k) {sevm : Sevm} {h : B256} (index n : Nat) (b : Devm) (M : Mem)
    (bound : index + n ≤ k.capN) (aligned : M.size % 32 = 0) (fits : M.size ≤ m.alloc) :
    (k.fold sevm h index n b M).memory.size % 32 = 0 ∧
    (k.fold sevm h index n b M).memory.size ≤ m.alloc ∧
    (k.fold sevm h index n b M).charges + calculateMemoryGasCost M.size ≤
      n * (23 + k.bodyFixed + k.slots * gasColdSload + gVerylow * k.writes) +
        calculateMemoryGasCost (k.fold sevm h index n b M).memory.size := by
  induction n generalizing index b M with
  | zero => exact ⟨aligned, fits, by simp only [fold]; omega⟩
  | succ n ih =>
    let i := index.toB256
    let rd := b.getStorVal sevm.currentTarget
    let stage := k.stage rd h i
    have hsize : (stage.applyMemory M).size = memExtsSize M.size stage.footprint :=
      MemoryStage.applyMemory_size stage M aligned
    have hal := MemoryStage.applyMemory_aligned stage M aligned
    have hfit : (stage.applyMemory M).size ≤ m.alloc := by
      rw [hsize]
      exact MemoryStage.memExtsSize_le m.aligned fits (m.windows rd h index (by omega))
    have hgas := MemoryStage.selectedGas_eq stage M aligned
    have hmono := Jaune.calculateMemoryGasCost_mono (Lift.memExtsSize_ge M.size stage.footprint)
    rw [← hsize] at hmono
    have hlen : stage.length = k.writes := k.stage_length rd h i
    rw [hlen] at hgas
    have hreads := readsGas_le sevm b (k.keys h i)
    rw [k.keys_length] at hreads
    obtain ⟨a1, a2, a3⟩ := ih (index + 1) (readsBase sevm b (k.keys h i)) (stage.applyMemory M)
      (by omega) hal hfit
    refine ⟨a1, a2, ?_⟩
    change 23 + k.bodyFixed + readsGas sevm b (k.keys h i) + MemoryStage.selectedGas stage M +
        (k.fold sevm h (index + 1) n (readsBase sevm b (k.keys h i)) (stage.applyMemory M)).charges +
        calculateMemoryGasCost M.size ≤ (n + 1) * _ +
      calculateMemoryGasCost
        (k.fold sevm h (index + 1) n (readsBase sevm b (k.keys h i)) (stage.applyMemory M)).memory.size
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem drainCount_le (cap h t : B256) : (drainCount cap h t).toNat ≤ cap.toNat := by
  unfold drainCount
  split
  · rename_i hlt
    exact Nat.le_of_lt (B256.toNat_lt_toNat hlt)
  · exact Nat.le_refl _

theorem count_le (sevm : Sevm) (b : Devm) : (k.count sevm b).toNat ≤ k.capN := by
  rw [← k.cap_word]
  exact drainCount_le _ _ _

theorem outLen_le (m : SysMemory k) (sevm : Sevm) (b : Devm) :
    (0 : B256).toNat + (k.outLen sevm b).toNat ≤ m.alloc := by
  have hc := k.count_le sevm b
  have hmul : (k.outLen sevm b).toNat ≤ m.lenN * (k.count sevm b).toNat := by
    unfold outLen
    rw [B256.toNat_mul, m.len_word]
    exact Nat.mod_le _ _
  have h1 := Nat.mul_le_mul_left m.lenN hc
  have h2 := m.len_le
  have h0 : (0 : B256).toNat = 0 := rfl
  omega

/-- Everything of a frame's charge but the excess update and the final stores. -/
theorem prefix_le (m : SysMemory k) (sevm : Sevm) (b : Devm) :
    chargedRetExt (k.drain sevm b).memory 0 (k.outLen sevm b) +
        bookGas sevm (k.drain sevm b).base (rd sevm b 2) (k.count sevm b) (rd sevm b 3) +
        (k.drain sevm b).charges + 23 + setupGas k.shape.cap.word sevm b + dispatchGas +
        (113 + 2 * gasColdSload + 2 * (gasColdSload + amsterdamStateGasRules.storageWrite)) ≤
      k.frameBound m.alloc := by
  have hcap := count_le (k := k) sevm b
  obtain ⟨_, hfit, hcharges⟩ := fold_charges m (sevm := sevm) (h := rd sevm b 2) 0
    (k.count sevm b).toNat (setupBase sevm b) .empty (by omega) rfl (Nat.zero_le _)
  have hMem : chargedRetExt (k.drain sevm b).memory 0 (k.outLen sevm b) +
      calculateMemoryGasCost (k.drain sevm b).memory.size ≤ calculateMemoryGasCost m.alloc := by
    unfold chargedRetExt
    have hexts : memExtSize (k.drain sevm b).memory.size (0 : B256).toNat (k.outLen sevm b).toNat ≤
        m.alloc := by
      have := MemoryStage.memExtsSize_le (windows := [((0 : B256).toNat, (k.outLen sevm b).toNat)])
        (initial := (k.drain sevm b).memory.size) m.aligned hfit (by
          intro w hw
          rw [List.mem_singleton] at hw
          subst hw
          exact outLen_le m sevm b)
      exact this
    have mono1 := Jaune.calculateMemoryGasCost_mono hexts
    have mono2 := Jaune.calculateMemoryGasCost_mono
      (Lift.memExtSize_ge (k.drain sevm b).memory.size (0 : B256).toNat (k.outLen sevm b).toNat)
    omega
  have hmul := Nat.mul_le_mul_right
    (23 + k.bodyFixed + k.slots * gasColdSload + gVerylow * k.writes) hcap
  have hBook : bookGas sevm (k.drain sevm b).base (rd sevm b 2) (k.count sevm b)
      (rd sevm b 3) ≤ 46 + 2 * (gasColdSload + amsterdamStateGasRules.storageWrite) := by
    unfold bookGas
    split
    · have c1 := sstoreCostA_le A sevm (k.drain sevm b).base 2 0
      have c2 := sstoreCostA_le A sevm (afterSstoreA A sevm (k.drain sevm b).base 2 0) 3 0
      omega
    · have c1 := sstoreCostA_le A sevm (k.drain sevm b).base 2 (rd sevm b 2 + k.count sevm b)
      omega
  have hSetup : setupGas k.shape.cap.word sevm b ≤ 46 + 2 * gasColdSload := by
    have c1 := sloadCost_le sevm b 3
    have c2 := sloadCost_le sevm (afterSloadA sevm b 3) 2
    unfold setupGas
    split <;> omega
  have hDispatch : dispatchGas = 21 := rfl
  simp only [frameBound]
  simp only [drain] at hcharges hMem hBook ⊢
  omega

/-- **The rule-relative gas bound.** -/
theorem frameCost_le (m : SysMemory k) (sevm : Sevm) (b : Devm) :
    k.frameCost sevm b ≤ k.frameBound m.alloc := by
  have hp := prefix_le m sevm b
  have hFinal : finalGas sevm (k.excessRead sevm b) (k.excessStored sevm b) ≤
      18 + 2 * (gasColdSload + amsterdamStateGasRules.storageWrite) := by
    have c1 := sstoreCostA_le A sevm (k.excessRead sevm b) 0 (k.excessStored sevm b)
    have c2 := sstoreCostA_le A sevm
      (afterSstoreA A sevm (k.excessRead sevm b) 0 (k.excessStored sevm b)) 1 0
    simp only [finalGas]
    omega
  have hExcess : excessGas k.shape.fixed sevm (k.booked sevm b) ≤ 95 + 2 * gasColdSload := by
    have c1 := sloadCost_le sevm (k.booked sevm b) 0
    have c2 := sloadCost_le sevm (afterSloadA sevm (k.booked sevm b) 0) 1
    have c4 := k.shape.fixed_le ((k.booked sevm b).getStorVal sevm.currentTarget 0)
      ((k.booked sevm b).getStorVal sevm.currentTarget 1)
    simp only [excessGas]
    omega
  simp only [frameCost]
  omega

/-! ## The envelope -/

section Envelope

variable {benv : Benv} {target : Adr} {data : Bytes}

/-- The prepared base is ready for the frame's four stores, from the real grant. -/
theorem ready_base (hfork : benv.stat.fork = .amsterdam) :
    Ready (initSevm (systemCallMsg benv target k.code data))
      (systemCallBase (systemCallMsg benv target k.code data)) [2, 3, 0, 1] where
  error := systemCallBase_error _
  refund := by rw [systemCallBase_refundCounter]
  spill := (systemCallBase_stateGas hfork).1
  reservoir := by
    rw [(systemCallBase_stateGas hfork).2]
    decide
  clean := fun k' _ => systemCallBase_orig rfl _ k'

/-- The post frame at the message's gas. -/
abbrev callPost (k : SysPath) (benv : Benv) (target : Adr) : Devm :=
  let s := initSevm (systemCallMsg benv target k.code [])
  let b := systemCallBase (systemCallMsg benv target k.code [])
  k.framePost s b (systemTransactionGas - k.frameCost s b)

/-- **The checked system call over the whole frame, from any storage.** -/
theorem system_call (m : SysMemory k) (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode target = k.code) (hnonempty : k.code.isEmpty = false)
    (hdel : getDelegatedCodeAddress k.code = none) (hprecomp : ¬ amsterdamRules.isPrecomp target)
    (room : k.frameBound m.alloc + gCallStipend < systemTransactionGas) :
    processCheckedSystemTransaction benv target [] =
      .ok ((callPost k benv target).state,
        systemCallOutputA (systemCallMsg benv target k.code []) (callPost k benv target)) := by
  let s := initSevm (systemCallMsg benv target k.code [])
  let b := systemCallBase (systemCallMsg benv target k.code [])
  have hle := frameCost_le m s b
  have r := ready_base (k := k) (target := target) (data := []) hfork
  have hG : gCallStipend < systemTransactionGas - k.frameCost s b := by omega
  have run := k.frame_run (sevm := s) (b := b) hfork rfl rfl rfl r hG
  rw [show systemTransactionGas - k.frameCost s b + k.frameCost s b = systemTransactionGas by omega,
    show St b [] .empty systemTransactionGas = b from systemCallBase_St] at run
  have hexec : Nonempty (Exec 0 s b (.ok (k.framePost s b (systemTransactionGas - k.frameCost s b)))) :=
    lift_exact_noExec k.check k.jumps rfl k.noExec ⟨_, k.root, run⟩
  have hrun := (exec_iff_exec_eq _ _ _ _).mp hexec
  have rSetup : Ready s (setupBase s b) [2, 3, 0, 1] := (r.sload 3).sload 2
  have rDrain := k.fold_ready (h := SysPath.rd s b 2) 0 (k.count s b).toNat (M := .empty) rSetup
  have rBooked := ready_book rDrain (SysPath.rd s b 2) (k.count s b) (SysPath.rd s b 3)
  have rRead : Ready s (k.excessRead s b) [0, 1] := (rBooked.sload 0).sload 1
  have rEnd := (rRead.sstore (by decide) (k.excessStored s b)).sstore (by decide) (0 : B256)
  exact processCheckedSystemTransaction_amsterdam_of_exec hfork installed hnonempty hdel hprecomp
    hrun rEnd.error rEnd.refund

end Envelope

/-! ## The post state -/

end SysPath

/-- The call's regular gas stays within `B`: it ends with at most the 30,000,000 it started with, so the
subtraction is exact, and spends at most `B` of them. State gas is excluded: it draws on the reservoir of
16 × `storageSet` and never touches `gasLeft`. -/
def RegularGasWithin (gasLeft B : Nat) : Prop :=
  gasLeft ≤ systemTransactionGas ∧ systemTransactionGas - gasLeft ≤ B

/-- The exact post state of a request system call on empty calldata: pointers, excess and count
updated as the bytes define, nothing else. -/
def sysState (p : SysShape) (σ : State) (a : Adr) : State :=
  let rd : B256 → B256 := fun key => (σ.getStor a).get key
  let c := drainCount p.cap.word (rd 2) (rd 3)
  let σ1 := if rd 2 + c = rd 3 then (σ.setStorVal a 2 0).setStorVal a 3 0
    else σ.setStorVal a 2 (rd 2 + c)
  (σ1.setStorVal a 0 (p.next (rd 0) (rd 1))).setStorVal a 1 0

/-- A request system call's post state changes no account's code, so a later call still sees its own. -/
theorem sysState_getCode (p : SysShape) (σ : State) (a x : Adr) :
    (sysState p σ a).getCode x = σ.getCode x := by
  simp only [sysState]
  split <;> simp only [State.getCode_setStorVal]

theorem getStor_setStorVal_other (w : State) {owner a : Adr} (k v : B256) (h : owner ≠ a) :
    (w.setStorVal owner k v).getStor a = w.getStor a := by
  show ((w.setStorVal owner k v).get a).stor = _
  rw [State.get_setStorVal_ne _ _ _ h]
  rfl

/-- A storage write leaves every balance alone. -/
theorem bal_setStorVal (w : State) (owner : Adr) (key value : B256) (x : Adr) :
    ((w.setStorVal owner key value).get x).bal = (w.get x).bal := by
  by_cases h : owner = x
  · subst h
    rw [State.get_setStorVal_self]
  · rw [State.get_setStorVal_ne _ _ _ h]

theorem sysState_bal (p : SysShape) (σ : State) (a x : Adr) :
    ((sysState p σ a).get x).bal = (σ.get x).bal := by
  simp only [sysState]
  split <;> simp only [bal_setStorVal]

namespace SysPath

variable {k : SysPath}

theorem setupBase_state (sevm : Sevm) (b : Devm) : (setupBase sevm b).state = b.state := by
  simp only [setupBase, afterSloadA_state]

theorem drain_state (sevm : Sevm) (b : Devm) : (k.drain sevm b).base.state = b.state := by
  simp only [drain, fold_state, setupBase_state]

theorem bookBase_state (sevm : Sevm) (q : Devm) (h c t : B256) :
    (bookBase sevm q h c t).state =
      if h + c = t then (q.state.setStorVal sevm.currentTarget 2 0).setStorVal sevm.currentTarget 3 0
      else q.state.setStorVal sevm.currentTarget 2 (h + c) := by
  unfold bookBase
  split <;> simp only [afterSstoreA_state]

theorem getStorVal_of_state {d : Devm} {σ : State} {a : Adr} (h : d.state = σ) (key : B256) :
    d.getStorVal a key = (σ.getStor a).get key := by
  subst h
  rfl

/-- Reading a slot the pointer stores do not touch. -/
theorem state_get_ne (σ : State) (a : Adr) {key k' : B256} (v : B256) (h : key ≠ k') :
    ((σ.setStorVal a key v).getStor a).get k' = (σ.getStor a).get k' := by
  rw [State.getStor_setStorVal_self, Stor.get_set_ne _ h]

theorem booked_get {sevm : Sevm} {b : Devm} {key : B256} (h2 : (2 : B256) ≠ key)
    (h3 : (3 : B256) ≠ key) :
    (k.booked sevm b).getStorVal sevm.currentTarget key = rd sevm b key := by
  unfold booked
  rw [getStorVal_of_state (bookBase_state sevm _ _ _ _), drain_state]
  have hrd : rd sevm b key = (b.state.getStor sevm.currentTarget).get key := rfl
  rw [hrd]
  split
  · rw [state_get_ne _ _ _ h3, state_get_ne _ _ _ h2]
  · rw [state_get_ne _ _ _ h2]

/-- **The frame's post state.** -/
theorem framePost_state (sevm : Sevm) (b : Devm) (G : Nat) :
    (k.framePost sevm b G).state = sysState k.shape b.state sevm.currentTarget := by
  show (finalBase sevm (k.excessRead sevm b) (k.excessStored sevm b)).state = _
  simp only [finalBase, afterSstoreA_state, excessRead, afterSloadA_state, booked, bookBase_state,
    drain_state]
  have e0 : k.excessStored sevm b = k.shape.next (rd sevm b 0) (rd sevm b 1) := by
    simp only [excessStored]
    rw [booked_get (by decide) (by decide), booked_get (by decide) (by decide)]
  rw [e0]
  rfl

/-- A runtime that is no delegation: its length is not a designator's. -/
theorem not_delegated_of_size {code : ByteArray} (h : code.size ≠ eoaDelegatedCodeLength) :
    getDelegatedCodeAddress code = none := by
  simp only [getDelegatedCodeAddress]
  rw [ite_eq_right_iff.mpr]
  intro hd
  exact absurd hd.1 h

/-- **The checked system call with its exact post state and a regular-gas bound**, from any storage.
State gas is excluded; see `RegularGasWithin`. -/
theorem system_call_spec (m : SysMemory k) {B : Nat} {benv : Benv} {target : Adr}
    (hfork : benv.stat.fork = .amsterdam) (installed : benv.state.getCode target = k.code)
    (hnonempty : k.code.isEmpty = false) (hsize : k.code.size ≠ eoaDelegatedCodeLength)
    (hprecomp : ¬ amsterdamRules.isPrecomp target) (hB : k.frameBound m.alloc ≤ B)
    (room : B + gCallStipend < systemTransactionGas) :
    processCheckedSystemTransaction benv target [] =
      .ok (sysState k.shape benv.state target,
        systemCallOutputA (systemCallMsg benv target k.code []) (callPost k benv target)) ∧
    RegularGasWithin (callPost k benv target).gasLeft B := by
  have hle := frameCost_le m (initSevm (systemCallMsg benv target k.code []))
    (systemCallBase (systemCallMsg benv target k.code []))
  have hcall := system_call m hfork installed hnonempty (not_delegated_of_size hsize) hprecomp
    (by omega)
  have hstate : (callPost k benv target).state = sysState k.shape benv.state target :=
    framePost_state _ _ _
  rw [hstate] at hcall
  refine ⟨hcall, ?_⟩
  show systemTransactionGas - k.frameCost _ _ ≤ systemTransactionGas ∧
    systemTransactionGas - (systemTransactionGas - k.frameCost _ _) ≤ B
  omega

end SysPath

/-- A deployed runtime's facts for its system call: its address, its stated regular-gas bound, and that
the bound holds and leaves the stipend free of the 30,000,000 gas. -/
structure SysCall (k : SysPath) where
  memory : SysMemory k
  target : Adr
  bound : Nat
  nonempty : k.code.isEmpty = false
  size_ne : k.code.size ≠ eoaDelegatedCodeLength
  not_precompile : ¬ amsterdamRules.isPrecomp target
  bound_le : k.frameBound memory.alloc ≤ bound
  room : bound + gCallStipend < systemTransactionGas

/-- **A request system call under Amsterdam with its exact post state and a regular-gas bound**, from any
storage. State gas is excluded; see `RegularGasWithin`. -/
theorem SysCall.spec {k : SysPath} (c : SysCall k) {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode c.target = k.code) :
    processCheckedSystemTransaction benv c.target [] =
      .ok (sysState k.shape benv.state c.target,
        systemCallOutputA (systemCallMsg benv c.target k.code []) (SysPath.callPost k benv c.target)) ∧
    RegularGasWithin (SysPath.callPost k benv c.target).gasLeft c.bound :=
  SysPath.system_call_spec c.memory hfork installed c.nonempty c.size_ne c.not_precompile c.bound_le
    c.room

end Blanc.Lift.RequestSystem
