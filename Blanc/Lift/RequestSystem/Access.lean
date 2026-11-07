import Blanc.Lift.RequestSystem.Call
import Blanc.Lift.AmsterdamAccess
import Blanc.Lift.BalEffect

/-!
# A request system call's access-list entries, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

The slots a request contract's system call reads and writes, from any storage, and what its incorporation does to the
block's access-list builder at the call's index: exactly those slots, at that index. Slots' values come from the exact post
state `sysState`. The contract's own account read and any balance or nonce change are not stated here; the call changes none
of those fields.
-/

namespace Blanc.Lift.RequestSystem

open Jaune

namespace SysPath

variable (k : SysPath)

/-- The slots the drain loop reads, at head `h`, from record `index`, for `n` records. -/
def drainReads (h : B256) : Nat → Nat → List B256
  | _, 0 => []
  | index, n + 1 => k.keys h index.toB256 ++ drainReads h (index + 1) n

/-- The slots a system call writes: the pointers, then excess and count. -/
def sysWrites (h c t : B256) : List B256 := (if h + c = t then [2, 3] else [2]) ++ [0, 1]

/-- The slots a system call reads: tail and head, the drained records, and every slot it writes. -/
def sysReads (h c t : B256) : List B256 :=
  [3, 2] ++ k.drainReads h 0 c.toNat ++ sysWrites h c t

variable {k} {s : Sevm} {b : Devm}

theorem fold_access (hbal : s.benvStat.rules.bal.isSome = true) (h : B256) (index n : Nat) (d : Devm) (M : Mem) :
    Access s d (k.fold s h index n d M).base (k.drainReads h index n) [] := by
  induction n generalizing index d M with
  | zero => exact Access.refl s d
  | succ n ih =>
    exact ((Access.reads hbal _ d).trans (ih (index + 1) _ _)).congr (fun _ => Iff.rfl)
      (fun _ => by simp only [List.append_nil])

theorem chargedRet_access (s : Sevm) (d : Devm) (S : List B256) (M : Mem) (G : Nat) (i sz : B256) :
    Access s d (chargedRetPost d S M G i sz) [] [] :=
  Access.of_meta_world rfl rfl

/-- The frame's record. -/
theorem framePost_access (hbal : s.benvStat.rules.bal.isSome = true) (G : Nat) :
    Access s b (k.framePost s b G)
      (k.sysReads (rd s b 2) (k.count s b) (rd s b 3))
      (sysWrites (rd s b 2) (k.count s b) (rd s b 3)) := by
  have setup : Access s b (setupBase s b) ([3] ++ [2]) ([] ++ []) :=
    (Access.sload hbal b 3).trans (Access.sload hbal _ 2)
  have drain := fold_access (k := k) hbal (rd s b 2) 0 (k.count s b).toNat (setupBase s b) .empty
  have book : Access s (k.drain s b).base (k.booked s b)
      (if rd s b 2 + k.count s b = rd s b 3 then [2, 3] else [2])
      (if rd s b 2 + k.count s b = rd s b 3 then [2, 3] else [2]) := by
    unfold booked bookBase
    split
    · exact ((Access.sstore hbal _ _ 2 0).trans (Access.sstore hbal _ _ 3 0)).congr
        (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    · exact Access.sstore hbal _ _ 2 _
  have reads01 : Access s (k.booked s b) (k.excessRead s b) ([0] ++ [1]) ([] ++ []) :=
    (Access.sload hbal _ 0).trans (Access.sload hbal _ 1)
  have final : Access s (k.excessRead s b) (finalBase s (k.excessRead s b) (k.excessStored s b))
      ([0] ++ [1]) ([0] ++ [1]) :=
    (Access.sstore hbal _ _ 0 _).trans (Access.sstore hbal _ _ 1 0)
  have ret : Access s (finalBase s (k.excessRead s b) (k.excessStored s b)) (k.framePost s b G) [] [] :=
    chargedRet_access s _ _ _ _ _ _
  refine (setup.trans (drain.trans (book.trans (reads01.trans (final.trans ret))))).congr
    (fun x => ?_) (fun x => ?_)
  · simp only [sysReads, sysWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    generalize (x ∈ k.drainReads _ _ _) = P
    generalize (x ∈ (if rd s b 2 + k.count s b = rd s b 3 then ([2, 3] : List B256) else [2])) = Q
    generalize (x = (0 : B256)) = A
    generalize (x = (1 : B256)) = B
    generalize (x = (2 : B256)) = C
    generalize (x = (3 : B256)) = D
    tauto
  · simp only [sysWrites, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, false_or]

end SysPath

/-- **A request system call's access-list entries, under Amsterdam, from any storage.** The call returns the exact post
state. Incorporated at index `idx` into a builder where nothing earlier at this index captured or changed the slots it
writes: a slot among `sysWrites` whose value moved gains exactly one change, at `idx`, with its post value, and every other
slot's changes stay; a slot is recorded as read exactly if it already was or it is among `sysReads`; and no other account's
slots change. `h`, `c`, `tl` are the head, the drained count and the tail as the call found them. -/
theorem SysCall.bal {k : SysPath} (c : SysCall k) {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode c.target = k.code) (bal : BalBuilder) (idx : Nat) (ar : List Adr) :
    let σ := benv.state.getStor c.target
    let h := σ.get 2
    let tl := σ.get 3
    let cnt := drainCount k.shape.cap.word h tl
    ∃ out, processCheckedSystemTransaction benv c.target [] =
        .ok (sysState k.shape benv.state c.target, out) ∧
      ((∀ key ∈ SysPath.sysWrites h cnt tl, balStart bal idx c.target key = none) →
       (∀ key ∈ SysPath.sysWrites h cnt tl, ∀ e ∈ balChanges bal c.target key, e.1 ≠ idx) →
       let bal' := bal.incorporate idx benv.state (sysState k.shape benv.state c.target) ar
         out.storageReads.toList out.storageWrites.toList
       (∀ key, balChanges bal' c.target key =
         if key ∈ SysPath.sysWrites h cnt tl ∧
             (benv.state.get c.target).stor.get key ≠ ((sysState k.shape benv.state c.target).get c.target).stor.get key then
           balChanges bal c.target key ++ [(idx, ((sysState k.shape benv.state c.target).get c.target).stor.get key)]
         else balChanges bal c.target key) ∧
       (∀ key, balRead bal' c.target key ↔ balRead bal c.target key ∨ key ∈ k.sysReads h cnt tl) ∧
       (∀ a, a ≠ c.target → ∀ key,
         balChanges bal' a key = balChanges bal a key ∧ (balRead bal' a key ↔ balRead bal a key))) := by
  intro σ h tl cnt
  let M := systemCallMsg benv c.target k.code []
  let s := initSevm M
  let b := systemCallBase M
  have hbal : s.benvStat.rules.bal.isSome = true := by
    show (benv.beginTransaction).stat.rules.bal.isSome = true
    rw [amsterdam_rules (s := (benv.beginTransaction).stat) hfork]
    rfl
  obtain ⟨hcall, -⟩ := c.spec hfork installed
  have acc := SysPath.framePost_access (k := k) (s := s) (b := b) hbal (systemTransactionGas - k.frameCost s b)
  obtain ⟨hr0, hw0⟩ := systemCallBase_record M
  have hread : ∀ a key, (a, key) ∈ (SysPath.callPost k benv c.target).meta.storageReads ↔
      a = c.target ∧ key ∈ k.sysReads h cnt tl := by
    intro a key
    have hr : (a, key) ∈ (SysPath.callPost k benv c.target).meta.storageReads ↔
        (a, key) ∈ b.meta.storageReads ∨ ∃ x ∈ k.sysReads h cnt tl, (a, key) = (c.target, x) := acc.read (a, key)
    rw [hr, hr0]
    simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or, Prod.mk.injEq]
    constructor
    · rintro ⟨x, hx, rfl, rfl⟩
      exact ⟨rfl, hx⟩
    · rintro ⟨rfl, hx⟩
      exact ⟨key, hx, rfl, rfl⟩
  have hwrite : ∀ a key, (a, key) ∈ (SysPath.callPost k benv c.target).world.storageWrites ↔
      a = c.target ∧ key ∈ SysPath.sysWrites h cnt tl := by
    intro a key
    have hr : (a, key) ∈ (SysPath.callPost k benv c.target).world.storageWrites ↔
        (a, key) ∈ b.world.storageWrites ∨ ∃ x ∈ SysPath.sysWrites h cnt tl, (a, key) = (c.target, x) := acc.write (a, key)
    rw [hr, hw0]
    have hempty : (a, key) ∉ (benv.beginTransaction).storageWrites := Std.HashSet.not_mem_emptyWithCapacity
    have hnot : ¬ (a, key) ∈ (M).benv.storageWrites := hempty
    simp only [hnot, false_or, Prod.mk.injEq]
    constructor
    · rintro ⟨x, hx, rfl, rfl⟩
      exact ⟨rfl, hx⟩
    · rintro ⟨rfl, hx⟩
      exact ⟨key, hx, rfl, rfl⟩
  refine ⟨_, hcall, ?_⟩
  intro hfresh hclean bal'
  have ht := incorporate_keysets bal idx benv.state (sysState k.shape benv.state c.target) ar
    (SysPath.callPost k benv c.target).meta.storageReads (SysPath.callPost k benv c.target).world.storageWrites c.target
    (fun key hk => hfresh key ((hwrite _ _).mp hk).2) (fun key hk => hclean key ((hwrite _ _).mp hk).2)
  refine ⟨fun key => ?_, fun key => ?_, fun a hne key => ?_⟩
  · refine (ht.1 key).trans ?_
    simp only [hwrite, true_and]
  · refine (ht.2 key).trans ?_
    simp only [hread, true_and]
  · have ho := incorporate_keysets bal idx benv.state (sysState k.shape benv.state c.target) ar
      (SysPath.callPost k benv c.target).meta.storageReads (SysPath.callPost k benv c.target).world.storageWrites a
      (fun key hk => absurd ((hwrite _ _).mp hk).1 hne) (fun key hk => absurd ((hwrite _ _).mp hk).1 hne)
    refine ⟨(ho.1 key).trans ?_, (ho.2 key).trans ?_⟩
    · simp only [hwrite, hne, false_and, ↓reduceIte]
    · simp only [hread, hne, false_and, or_false]

end Blanc.Lift.RequestSystem
