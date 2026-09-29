import Blanc.Lift.CreationOps
import Blanc.Lift.ExactWalkOps
import Blanc.AddressSlotProofs
import Blanc.Lift.MapSlot

/-!
# Gas-exact walk kit for solc-0.4-style runtimes

The forward (`rx_*`) steps and the memory invariant the writer entries of a solc 0.4 contract
need beyond `ExactWalk.lean`, `ExactWalkOps.lean` and `WalkSteps.lean`, and a few tactic macros that
apply one step to the head instruction of a `SFunc.RunExact` goal.

* `FpMem n M`: `M` is word-aligned, `n ≥ 96` bytes long, and holds the free-memory pointer `0x60`
  at `0x40`; kept for an arbitrary `M`, so no concrete image is unfolded.  A word written at `0` or
  `0x20` (the hashing scratch) or at `0x60` (the event and result words) keeps it
  (`FpMem.write`), the first write at `0x60` grows `96` to `128` bytes (`FpMem.write_out`), and
  a word just written reads back (`FpMem.readback`).
* memory steps over it: `MSTORE` (`rx_mstoreF`, `rx_mstoreOut`), the free-pointer `MLOAD`
  (`rx_mloadFp`), the mapping-slot `KECCAK256` of the two scratch words (`rx_keccakF`,
  `mapSlot`), `LOG2`/`LOG3` of the word at `0x60` (`rx_log2W`, `rx_log3W`), `RETURN` of it
  (`rx_returnW`);
* `PUSH20 0xff..ff; AND` (`rx_mask20`, `rx_mask20_adr`), `SWAP4` (`rx_swap4`), `STOP` (`rx_stop`);
* `scratchW M a c`, the image after one hash's two scratch writes (`FpMem.scratchW`);
* tactic macros `rdest`, `rpush`, `rdup`, `rswap`, `rpop`, `radd`, `rsub`, `riszero`, `rmask`,
  `rmst`, `rmld`, `rkec`, `rhash` (the whole mapping-slot hash after the key is on the stack), `rsload`,
  `rsstore`, `rsstoreO` (an `SSTORE` whose sentry follows by `omega`), `rlog2`, `rlog3`, each applying the step lemma for
  the head instruction and closing its side goals.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

macro "rroom" : tactic => `(tactic| (first | omega | (simp <;> omega)))

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome}

/-- `PUSH20 0xff..ff; AND`: the address projection of the top word. -/
theorem rx_mask20 {x : B256} (hroom : S.length < 1023)
    (k : SFunc.RunExact fs sevm (St b (x.toAdr.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: S) M (G + 6))
      (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide))
        (.next (.reg .and) f)) o := by
  refine rx_push rfl (by rroom) ?_
  exact rx_and (ff20_and_word x) (by rroom) k

/-- The same on a word that already is an address. -/
theorem rx_mask20_adr (a : Adr) (hroom : S.length < 1023)
    (k : SFunc.RunExact fs sevm (St b (a.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (a.toB256 :: S) M (G + 6))
      (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide))
        (.next (.reg .and) f)) o :=
  rx_mask20 (x := a.toB256) hroom (by rw [toAdr_toB256]; exact k)

theorem rx_swap4 {x y z w v : B256}
    (k : SFunc.RunExact fs sevm (St b (v :: y :: z :: w :: x :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (x :: y :: z :: w :: v :: S) M (G + 3))
      (.next (.reg (.swap 3)) f) o :=
  rx_swap (n := 3) rfl k

end Steps
macro "rdest" : tactic => `(tactic| refine rx_dest ?_)
macro "rdup" : tactic => `(tactic| refine rx_dup rfl (by rroom) ?_)
macro "rswap" : tactic => `(tactic| first
  | refine rx_swap1 ?_
  | refine rx_swap2 ?_
  | refine rx_swap3 ?_
  | refine rx_swap4 ?_)
macro "rpop" : tactic => `(tactic| refine rx_pop ?_)
macro "rmask" : tactic => `(tactic| first
  | refine rx_mask20_adr _ (by rroom) ?_
  | refine rx_mask20 (by rroom) ?_)
macro "rpush" : tactic => `(tactic| first
  | refine rx_push (w := 0) (by decide) (by rroom) ?_
  | refine rx_push (w := 1) (by decide) (by rroom) ?_
  | refine rx_push (w := 3) (by decide) (by rroom) ?_
  | refine rx_push (w := 4) (by decide) (by rroom) ?_
  | refine rx_push (w := 32) (by decide) (by rroom) ?_
  | refine rx_push (w := 64) (by decide) (by rroom) ?_
  | refine rx_push rfl (by rroom) ?_)
macro "radd" : tactic => `(tactic| first
  | refine rx_add' (v := 32) (by decide) (by rroom) ?_
  | refine rx_add' (v := 64) (by decide) (by rroom) ?_
  | refine rx_add' (v := 36) (by decide) (by rroom) ?_
  | refine rx_add' (v := 68) (by decide) (by rroom) ?_
  | refine rx_add' (v := 128) (by decide) (by rroom) ?_
  | refine rx_add (by rroom) ?_)


/-! ## The scratch memory

A solc 0.4 runtime writes whole words at `0`, `0x20` (the hashing scratch) or, once each for the event
and the result word, at `0x60`, in a memory whose free-memory pointer word (`0x40`) is `0x60`. -/

structure FpMem (n : Nat) (M : Mem) : Prop where
  size : M.size = n
  n32 : n % 32 = 0
  ge : 96 ≤ n
  wf : Mem.Wf M
  reads : ∃ bs, Mem.Reads M bs ∧ bs.sliceD 64 32 0 = (0x60 : B256).toBytes

/-- The memory after the dispatcher's `mstore(0x40, 0x60)` on empty memory. -/
theorem FpMem.init : FpMem 96 (Mem.empty.write 64 (0x60 : B256).toBytes) := by
  refine ⟨?_, by decide, le_refl _, Mem.wf_empty.write _ _,
    ⟨_, Mem.reads_empty.write Mem.wf_empty 64 _, sliceD_word_same _ _ _⟩⟩
  rw [Mem.size_write_word_at]; rfl

theorem Mem.size_write_word_of_le {μ : Mem} {n i : Nat} {w : B256} (hs : μ.size = n)
    (hw : i + 32 ≤ n) : (μ.write i w.toBytes).size = n := by
  rw [Mem.size_write_word_at, hs]; simp [hw]

theorem FpMem.write {n : Nat} {M : Mem} (h : FpMem n M) (i : Nat) (v : B256) (hi : i + 32 ≤ n)
    (hd : i + 32 ≤ 64 ∨ 96 ≤ i) : FpMem n (M.write i v.toBytes) := by
  obtain ⟨bs, hr, hf⟩ := h.reads
  refine ⟨Mem.size_write_word_of_le h.size hi, h.n32, h.ge, h.wf.write _ _,
    ⟨Bytes.writeAt bs i v.toBytes, hr.write h.wf i _, ?_⟩⟩
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
  exact hf

theorem FpMem.write_out {M : Mem} (h : FpMem 96 M) (v : B256) : FpMem 128 (M.write 96 v.toBytes) := by
  obtain ⟨bs, hr, hf⟩ := h.reads
  refine ⟨?_, by decide, by decide, h.wf.write _ _,
    ⟨Bytes.writeAt bs 96 v.toBytes, hr.write h.wf 96 _, ?_⟩⟩
  · rw [Mem.size_write_word_at, h.size]; decide
  · rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
    exact hf

theorem FpMem.fp {n : Nat} {M : Mem} (h : FpMem n M) : (M.read 64 32).1 = (0x60 : B256).toBytes := by
  obtain ⟨bs, hr, hf⟩ := h.reads
  rw [hr.read]; exact hf

theorem FpMem.read_self {n : Nat} {M : Mem} (h : FpMem n M) {i sz : Nat} (hw : i + sz ≤ n) :
    (M.read i sz).2 = M :=
  Mem.read_snd_eq_self (by rw [h.size]; exact memExtSize_of_le h.n32 hw)

theorem FpMem.readback {n : Nat} {M : Mem} (h : FpMem n M) (i : Nat) (v : B256) :
    ((M.write i v.toBytes).read i 32).1 = v.toBytes := by
  obtain ⟨bs, hr, -⟩ := h.reads
  rw [(hr.write h.wf i v.toBytes).read, sliceD_word_same]

theorem FpMem.extCost {n : Nat} {M : Mem} (h : FpMem n M) {b : Devm} {S : List B256} {G i sz : Nat}
    (hw : i + sz ≤ n) : (St b S M G).extCost [⟨i, sz⟩] = 0 :=
  Devm.extCost_zero_of_le (by rw [h.size]; exact h.n32) (by rw [h.size]; exact hw)

/-- The image after the two scratch writes of one mapping-slot hash: `key` at `0`, `base` at `0x20`. -/
def scratchW (M : Mem) (a c : B256) : Mem := (M.write 0 a.toBytes).write 32 c.toBytes

theorem FpMem.scratchW {n : Nat} {M : Mem} (h : FpMem n M) (a c : B256) :
    FpMem n (scratchW M a c) :=
  (h.write 0 a (by have := h.ge; omega) (by omega)).write 32 c (by have := h.ge; omega) (by omega)

theorem scratch_read (M0 : Mem) (a c : B256) :
    (((M0.write 0 a.toBytes).write 32 c.toBytes).read 0 64).1 = a.toBytes ++ c.toBytes :=
  Mem.read_two_word_writes_at_raw M0 0 a c

section MemSteps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome} {n : Nat}

/-- `MSTORE` of a word inside the memory, no expansion; the invariant is carried. -/
theorem rx_mstoreF {i v : B256} {i0 : Nat} (hM : FpMem n M) (hi : i.toNat = i0)
    (hin : i0 + 32 ≤ n) (hd : i0 + 32 ≤ 64 ∨ 96 ≤ i0)
    (k : FpMem n (M.write i0 v.toBytes) →
      SFunc.RunExact fs sevm (St b S (M.write i0 v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + 3)) (.next (.reg .mstore) f) o := by
  refine rx_mstore (c := 3) ?_ (by rw [hi]) (by rw [hi] at *; exact k (hM.write i0 v hin hd))
  rw [hi, hM.extCost (by omega)]; rfl

/-- `MSTORE` of the first word past the free-memory pointer word, at `0x60`: one word of expansion. -/
theorem rx_mstoreOut {i v : B256} (hM : FpMem 96 M) (hi : i.toNat = 96)
    (k : FpMem 128 (M.write 96 v.toBytes) →
      SFunc.RunExact fs sevm (St b S (M.write 96 v.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (i :: v :: S) M (G + 6)) (.next (.reg .mstore) f) o := by
  refine rx_mstore (c := 6) ?_ (by rw [hi]) (by rw [hi] at *; exact k (hM.write_out v))
  rw [hi, St.extCost_eq hM.size]; decide

/-- `MLOAD` of the free-memory pointer word. -/
theorem rx_mloadFp {i : B256} (hM : FpMem n M) (hi : i.toNat = 64) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (0x60 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: S) M (G + 3)) (.next (.reg .mload) f) o := by
  refine rx_mload (c := 3) ?_ ?_ ?_ hroom k
  · rw [hi, hM.extCost (by have := hM.ge; omega)]; rfl
  · rw [hi, hM.fp, B256.toB256_toBytes]
  · rw [hi]; exact hM.read_self (by have := hM.ge; omega)

/-- `KECCAK256` of the two scratch words. -/
theorem rx_keccakF {M0 : Mem} {a c i sz : B256}
    (hM : FpMem n ((M0.write 0 a.toBytes).write 32 c.toBytes)) (hi : i.toNat = 0)
    (hsz : sz.toNat = 64) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (mapSlot a c :: S) ((M0.write 0 a.toBytes).write 32 c.toBytes) G)
      f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) ((M0.write 0 a.toBytes).write 32 c.toBytes) (G + 42))
      (.next (.reg .keccak256) f) o := by
  refine rx_keccak (c := 42) ?_ ?_ ?_ hroom k
  · rw [hi, hsz, hM.extCost (by have := hM.ge; omega)]; decide
  · rw [hi, hsz, scratch_read]; rfl
  · rw [hi, hsz]; exact hM.read_self (by have := hM.ge; omega)

/-- `LOG3` of the word just written at `0x60`. -/
theorem rx_log3W {M0 : Mem} {v i sz t1 t2 t3 : B256} (hstatic : sevm.isStatic = false)
    (hM0 : FpMem 96 M0) (hi : i.toNat = 96) (hsz : sz.toNat = 32)
    (k : SFunc.RunExact fs sevm
      (St (b.addLog ⟨sevm.currentTarget, [t1, t2, t3], v.toBytes⟩) S (M0.write 96 v.toBytes) G)
      f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: t1 :: t2 :: t3 :: S) (M0.write 96 v.toBytes) (G + 1756))
      (.next (.reg (.log 3)) f) o := by
  refine rx_log3 (c := 1756) hstatic ?_ ?_ ?_ k
  · rw [hi, hsz, (hM0.write_out v).extCost (by omega)]; decide
  · rw [hi, hsz]; exact hM0.readback 96 v
  · rw [hi, hsz]; exact (hM0.write_out v).read_self (by omega)

/-- `LOG2` of the word just written at `0x60`. -/
theorem rx_log2W {M0 : Mem} {v i sz t1 t2 : B256} (hstatic : sevm.isStatic = false)
    (hM0 : FpMem 96 M0) (hi : i.toNat = 96) (hsz : sz.toNat = 32)
    (k : SFunc.RunExact fs sevm
      (St (b.addLog ⟨sevm.currentTarget, [t1, t2], v.toBytes⟩) S (M0.write 96 v.toBytes) G)
      f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: t1 :: t2 :: S) (M0.write 96 v.toBytes) (G + 1381))
      (.next (.reg (.log 2)) f) o := by
  refine rx_log2 (c := 1381) hstatic ?_ ?_ ?_ k
  · rw [hi, hsz, (hM0.write_out v).extCost (by omega)]; decide
  · rw [hi, hsz]; exact hM0.readback 96 v
  · rw [hi, hsz]; exact (hM0.write_out v).read_self (by omega)

/-- `SLOAD` with its charge named: `c` is `sloadCost` at this state.  A walk over several storage
operations keeps each charge as a variable with such an equation, so that arithmetic on the
gas expression never sees the (large) states the charges depend on. -/
theorem rx_sload_selC {k' : B256} {c : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (hc : c = sloadCost sevm b k') (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm
      (St (afterSload sevm b k') (b.getStorVal sevm.currentTarget k' :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: S) M (G + c)) (.next (.reg .sload) f) o := by
  subst hc; exact rx_sload_sel hfork hroom k

/-- `SSTORE` with its charge named (see `rx_sload_selC`). -/
theorem rx_sstoreC {k' v : B256} {c : Nat} (hfork : CoveredFork sevm.benvStat.fork)
    (hc : c = sstoreCost sevm b k' v) (hsentry : gCallStipend < G + c)
    (hstatic : sevm.isStatic = false)
    (k : SFunc.RunExact fs sevm (St (afterSstore sevm b k' v) S M G) f o) :
    SFunc.RunExact fs sevm (St b (k' :: v :: S) M (G + c)) (.next (.reg .sstore) f) o := by
  subst hc; exact rx_sstore hfork hsentry hstatic k

/-- `STOP`: the state is kept. -/
theorem rx_stop {D : Devm} : SFunc.RunExact fs sevm D (.last .stop) (.halted D) := .last rfl

/-- `RETURN` of the word just written at `0x60`, over a memory that already reaches it. -/
theorem rx_returnW {M1 : Mem} {v i sz : B256} (hM : FpMem 128 M1) (hi : i.toNat = 96)
    (hsz : sz.toNat = 32) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) (M1.write 96 v.toBytes) G) (.last .return_)
      (.halted (((St b S (M1.write 96 v.toBytes) G).memRead i.toNat sz.toNat).2.withOutput
        v.toBytes)) := by
  have hM' := hM.write 96 v (by omega) (by omega)
  refine rx_return ?_ ?_
  · rw [hi, hsz]; exact hM'.extCost (by omega)
  · rw [hi, hsz]; exact hM.readback 96 v

end MemSteps


macro "rsub" : tactic => `(tactic| first
  | refine rx_sub' (v := 32) (by decide) (by rroom) ?_
  | refine rx_sub (by rroom) ?_)
macro "riszero" : tactic => `(tactic| first
  | refine rx_iszero (v := 0) (by decide) (by rroom) ?_
  | refine rx_iszero (v := 1) (by decide) (by rroom) ?_)
macro "rsload" : tactic => `(tactic| refine rx_sload_sel (by assumption) (by rroom) ?_)
macro "rsstore" : tactic => `(tactic|
  refine rx_sstore (by assumption) (by assumption) (by assumption) ?_)
macro "rsstoreO" : tactic => `(tactic|
  refine rx_sstore (by assumption) (by unfold gCallStipend at *; omega) (by assumption) ?_)
macro "rsloadC" : tactic => `(tactic|
  refine rx_sload_selC (by assumption) (by assumption) (by rroom) ?_)
/-- A sentry goal `gCallStipend < g + c₁ + …` follows from a hypothesis about a prefix `g`: peel the
charges (no arithmetic on their, possibly large, definitions). -/
macro "rsent" : tactic => `(tactic| (repeat (first | assumption | refine Nat.lt_add_right _ ?_)))
macro "rsstoreC" : tactic => `(tactic|
  refine rx_sstoreC (by assumption) (by assumption) (by rsent) (by assumption) ?_)
macro "rlog3" : tactic => `(tactic|
  refine rx_log3W (by assumption) (by assumption) (by decide) (by decide) ?_)
macro "rlog2" : tactic => `(tactic|
  refine rx_log2W (by assumption) (by assumption) (by decide) (by decide) ?_)
macro "rmst" i:num : tactic => `(tactic|
  (refine rx_mstoreF (i0 := $i) (by assumption) (by decide) (by omega) (by omega) (fun _ => ?_)))
macro "rkec" : tactic => `(tactic|
  refine rx_keccakF (by assumption) (by decide) (by decide) (by rroom) ?_)
macro "rmld" : tactic => `(tactic|
  refine rx_mloadFp (by assumption) (by decide) (by rroom) ?_)




macro "rhash" : tactic => `(tactic|
  (rmask; rmask; rdup; rmst 0; rpush; radd; rswap; rdup; rmst 32; rpush; radd; rpush; rkec))

end Blanc.Lift
