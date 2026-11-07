import Blanc.Lift.RequestSystem.Call
import Blanc.MemoryWindows

/-!
# What a request system call returns and leaves

`SysOutput` says a runtime's record writes extend the visible output by one record. `framePost_output`
then reads the whole return window, from any storage, as `drained`. `sysState_get` reads the post storage
slot by slot, and `runRequestContracts_step` is the request phase's call. Nothing here says which storage
is reachable, or that a stored record came from a real submission.
-/

namespace Blanc.Lift.RequestSystem

open Jaune

/-- Storage reads leave storage alone. -/
theorem readsBase_getStorVal (sevm : Sevm) (d : Devm) (keys : List B256) (a : Adr) :
    (readsBase sevm d keys).getStorVal a = d.getStorVal a := by
  funext key
  unfold Devm.getStorVal Devm.getAcct
  rw [readsBase_state]

theorem chargedRetPost_output (b : Devm) (S : List B256) (M : Mem) (G : Nat) (i sz : B256) :
    (chargedRetPost b S M G i sz).output = (M.read i.toNat sz.toNat).1 := rfl

/-- A runtime's records extend the return window one at a time. -/
structure SysOutput (k : SysPath) (m : SysMemory k) where
  /-- One record's returned bytes, from the storage read. -/
  record : (B256 → B256) → B256 → B256 → Bytes
  extend : ∀ rd h (i : Nat) image, i < k.capN →
    ((k.stage rd h i.toB256).applyImage image).sliceD 0 (m.lenN * (i + 1)) 0 =
      image.sliceD 0 (m.lenN * i) 0 ++ record rd h i.toB256

namespace SysOutput

variable {k : SysPath} {m : SysMemory k} (o : SysOutput k m)

/-- The first `n` records' returned bytes. -/
def drained (rd : B256 → B256) (h : B256) (n : Nat) : Bytes :=
  (List.range n).flatMap fun i => o.record rd h i.toB256

theorem drained_succ (rd : B256 → B256) (h : B256) (n : Nat) :
    o.drained rd h (n + 1) = o.drained rd h n ++ o.record rd h n.toB256 := by
  simp only [drained, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

/-- The loop's memory reads as the records drained so far. -/
theorem fold_image {sevm : Sevm} {h : B256} {rd : B256 → B256} (n : Nat) {index : Nat} {b : Devm}
    {M : Mem} {image : Bytes} (hrd : b.getStorVal sevm.currentTarget = rd) (wf : Mem.Wf M)
    (reads : Mem.Reads M image) (bound : index + n ≤ k.capN)
    (hp : image.sliceD 0 (m.lenN * index) 0 = o.drained rd h index) :
    ∃ final, Mem.Reads (k.fold sevm h index n b M).memory final ∧
      final.sliceD 0 (m.lenN * (index + n)) 0 = o.drained rd h (index + n) := by
  induction n generalizing index b M image with
  | zero => exact ⟨image, reads, hp⟩
  | succ n ih =>
    have step := MemoryStage.wf_reads (k.stage rd h index.toB256) wf reads
    have hp' : ((k.stage rd h index.toB256).applyImage image).sliceD 0 (m.lenN * (index + 1)) 0 =
        o.drained rd h (index + 1) := by
      rw [o.extend rd h index image (by omega), hp, drained_succ]
    have hnext : k.fold sevm h index (n + 1) b M =
        let post := k.fold sevm h (index + 1) n (readsBase sevm b (k.keys h index.toB256))
          ((k.stage rd h index.toB256).applyMemory M)
        ⟨post.base, post.memory, 23 + k.bodyFixed + readsGas sevm b (k.keys h index.toB256) +
          MemoryStage.selectedGas (k.stage rd h index.toB256) M + post.charges⟩ := by
      subst hrd
      rfl
    obtain ⟨final, hr, hs⟩ := ih (index := index + 1) (b := readsBase sevm b (k.keys h index.toB256))
      (M := (k.stage rd h index.toB256).applyMemory M)
      (image := (k.stage rd h index.toB256).applyImage image)
      ((readsBase_getStorVal _ _ _ _).trans hrd) step.1 step.2 (by omega) hp'
    rw [hnext]
    refine ⟨final, hr, ?_⟩
    rw [show index + (n + 1) = index + 1 + n by omega]
    exact hs

/-- The return window's length, as a number. -/
theorem outLen_toNat (sevm : Sevm) (b : Devm) :
    (k.outLen sevm b).toNat = m.lenN * (k.count sevm b).toNat := by
  have hc := k.count_le sevm b
  have h1 := Nat.mul_le_mul_left m.lenN hc
  unfold SysPath.outLen
  rw [B256.toNat_mul, m.len_word]
  exact Nat.mod_eq_of_lt (by have := m.len_le; have := m.alloc_lt; omega)

/-- **What the frame returns, from any storage.** -/
theorem framePost_output (sevm : Sevm) (b : Devm) (G : Nat) :
    (k.framePost sevm b G).output =
      o.drained (SysPath.rd sevm b) (SysPath.rd sevm b 2) (k.count sevm b).toNat := by
  have hrd : (setupBase sevm b).getStorVal sevm.currentTarget = SysPath.rd sevm b := by
    funext key
    exact SysPath.getStorVal_of_state (SysPath.setupBase_state sevm b) key
  obtain ⟨final, hr, hs⟩ := o.fold_image (sevm := sevm) (h := SysPath.rd sevm b 2)
    (k.count sevm b).toNat (index := 0) (b := setupBase sevm b) (M := .empty) (image := [])
    hrd Mem.wf_empty Mem.reads_empty (by have := k.count_le sevm b; omega) (by
      simp only [Nat.mul_zero]
      rfl)
  show ((k.drain sevm b).memory.read (0 : B256).toNat (k.outLen sevm b).toNat).1 = _
  rw [show (k.drain sevm b).memory =
    (k.fold sevm (SysPath.rd sevm b 2) 0 (k.count sevm b).toNat (setupBase sevm b) .empty).memory
    from rfl, hr.read, outLen_toNat (m := m), show (0 : B256).toNat = 0 from rfl]
  simpa only [Nat.zero_add] using hs

end SysOutput

/-! ## The call on a queue -/

/-- What the call returns, from any storage. -/
theorem SysOutput.callPost_output {k : SysPath} {m : SysMemory k} (o : SysOutput k m) (benv : Benv)
    (target : Adr) :
    (SysPath.callPost k benv target).output =
      o.drained (fun key => (benv.state.getStor target).get key) ((benv.state.getStor target).get 2)
        (drainCount k.shape.cap.word ((benv.state.getStor target).get 2)
          ((benv.state.getStor target).get 3)).toNat :=
  o.framePost_output _ _ _

/-- The storage a call reads, as a function. -/
abbrev storOf (σ : State) (a : Adr) : B256 → B256 := fun key => (σ.getStor a).get key

/-- The post storage, slot by slot. -/
theorem sysState_get (p : SysShape) (σ : State) (a : Adr) (key : B256) :
    ((sysState p σ a).getStor a).get key =
      let rd := storOf σ a
      let c := drainCount p.cap.word (rd 2) (rd 3)
      if (1 : B256) = key then 0
      else if (0 : B256) = key then p.next (rd 0) (rd 1)
      else if rd 2 + c = rd 3 then
        (if (3 : B256) = key then 0 else if (2 : B256) = key then 0 else rd key)
      else (if (2 : B256) = key then rd 2 + c else rd key) := by
  simp only [sysState]
  split <;> simp only [State.getStor_setStorVal_self, Stor.get_set_ite]

/-- **The request phase's call is the empty-data call.** One step of `runRequestContracts` is exactly
`processCheckedSystemTransaction benv addr []`, whatever the contract: the code's calldata latch needs
nonempty calldata, so it is unreachable from the request phase. -/
theorem runRequestContracts_step {idx : Nat} {ty : UInt8} {addr : Adr} {rest : List (UInt8 × Adr)}
    {benv : Benv} {acc : List Bytes} {bal : BalBuilder} {state : State} {out : MsgCallOutput}
    (h : processCheckedSystemTransaction benv addr [] = .ok (state, out)) :
    runRequestContracts idx ((ty, addr) :: rest) benv acc bal =
      runRequestContracts idx rest (benv.withState state)
        (if out.returnData.length > 0 then acc ++ [[ty] ++ out.returnData] else acc)
        (match benv.stat.rules.bal with
          | none => bal
          | some _ => bal.incorporate idx benv.state state (addr :: out.accountReads.toList)
              out.storageReads.toList out.storageWrites.toList) := by
  simp only [runRequestContracts, h, bind, Except.bind]
  rfl

/-- Slot 0 after a call on empty calldata is the shape's stored excess, never a calldata latch's write. -/
theorem sysState_get_zero (p : SysShape) (σ : State) (a : Adr) :
    ((sysState p σ a).getStor a).get 0 = p.next ((σ.getStor a).get 0) ((σ.getStor a).get 1) := by
  rw [sysState_get]
  dsimp only
  rw [if_neg (by decide), if_pos rfl]

/-- An account with this code and storage, in any state: the installation and storage premises can be
met together. -/
theorem install_witness (σ : State) (a : Adr) (code : ByteArray) (s : Stor) :
    (σ.set a { σ.get a with code := code, stor := s }).getCode a = code ∧
      storOf (σ.set a { σ.get a with code := code, stor := s }) a = fun key => s.get key := by
  constructor
  · unfold State.getCode
    rw [State.get_set_self]
  · funext key
    show ((σ.set a { σ.get a with code := code, stor := s }).get a).stor.get key = _
    rw [State.get_set_self]

end Blanc.Lift.RequestSystem
