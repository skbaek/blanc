import Blanc.Lift.UniswapV2Pair.SkimWalk
import Blanc.Lift.UniswapV2Pair.SkimTransferWalk

/-! Skim's second balance query and second transfer after transfer0 moved the free
pointer, the unlock tail, and the complete raw pc0 inverse. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- A well-formed memory whose free-pointer word reads `p`; no allocation size is tracked. -/
def SkimPtr (p : B256) (M : Mem) : Prop :=
  Mem.Wf M ∧ Bytes.toB256 (M.read 64 32).1 = p

theorem SkimPtr.of_ptrMem {p : B256} {n : Nat} {M : Mem} (h : PtrMem p n M) : SkimPtr p M :=
  ⟨h.wf, h.word⟩

/-- Any byte write at or above the pointer word's end keeps the pointer. -/
theorem SkimPtr.write {p : B256} {M : Mem} (h : SkimPtr p M) (i : Nat) (bs : Bytes)
    (far : 96 ≤ i) : SkimPtr p (M.write i bs) := by
  refine ⟨h.1.write i bs, ?_⟩
  rw [(Mem.reads_data M |>.write h.1 i bs).read,
    Bytes.sliceD_writeAt_before _ _ 64 32 i (by omega), ← (Mem.reads_data M).read]
  exact h.2

theorem SkimPtr.extend {p : B256} {M : Mem} (h : SkimPtr p M) (i n : Nat) :
    SkimPtr p (M.read i n).2 :=
  ⟨h.1.extend i n, h.2⟩

theorem SkimPtr.set {p : B256} {M : Mem} (h : SkimPtr p M) (q : B256) :
    SkimPtr q (M.write 64 q.toBytes) := by
  refine ⟨h.1.write _ _, ?_⟩
  rw [(Mem.reads_data M |>.write h.1 64 q.toBytes).read, Bytes.readWord_writeAt_self]

/-- After transfer0 the free pointer is292 (empty reply) or the modular reply bump. -/
theorem skimAfterFirst_ptr {M1 : Mem} {a0 toWord : B256} {reply : Bytes}
    (mem : PtrMem 128 192 M1) :
    SkimPtr (if reply = [] then 292 else 292 + ((reply.length.toB256 + 63) &&& ~~~31))
      (if reply = [] then safeTransfer_call128Memory M1 a0 toWord else
        safeTransfer_reply292Memory (safeTransfer_call128Memory M1 a0 toWord) reply) := by
  have h0 := SkimPtr.of_ptrMem mem
  have call : SkimPtr 292 (safeTransfer_call128Memory M1 a0 toWord) := by
    unfold safeTransfer_call128Memory safeTransfer_payload128Memory
    dsimp only
    apply SkimPtr.write _ _ _ (by decide)
    apply SkimPtr.extend
    apply SkimPtr.write _ _ _ (by decide)
    apply SkimPtr.write _ _ _ (by decide)
    apply SkimPtr.write _ _ _ (by decide)
    refine SkimPtr.set (p := 192) ?_ 292
    apply SkimPtr.write _ _ _ (by decide)
    apply SkimPtr.write _ _ _ (by decide)
    apply SkimPtr.write _ _ _ (by decide)
    apply SkimPtr.write _ _ _ (by decide)
    apply SkimPtr.write _ _ _ (by decide)
    exact h0.set 192
  by_cases empty : reply = []
  · rw [ite_eq_left empty, ite_eq_left empty]
    exact call
  · rw [ite_eq_right empty, ite_eq_right empty]
    unfold safeTransfer_reply292Memory
    dsimp only
    apply SkimPtr.write _ _ _ (by decide)
    apply SkimPtr.write _ _ _ (by decide)
    exact call.set _

/-- The literal reserve1 reload and second balance request before its code guard. -/
def skimSecondLine : List Ninst := [
  .push [0x08] (by decide),
  .reg .sload,
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [0x04] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload,
  .push [0x1a, 0xca] (by decide),
  .reg (.swap 2),
  .reg (.dup 4),
  .reg (.swap 2),
  .reg (.dup 7),
  .reg (.swap 2),
  .push [0x1a, 0x26] (by decide),
  .reg (.swap 2),
  .push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.swap 0),
  .reg .div,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .reg (.swap 1),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 6),
  .reg .and,
  .reg (.swap 1),
  .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1),
  .push [0x24] (by decide),
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .add,
  .reg (.swap 2),
  .push [0x20] (by decide),
  .reg (.swap 2),
  .reg (.swap 0),
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 2),
  .reg (.swap 0),
  .reg .sub,
  .reg .add,
  .reg (.dup 1),
  .reg (.dup 6),
  .reg (.dup 0)]

/-- Second request memory: selector and Pair address at the moved free pointer. -/
def skimRequestMemory (M : Mem) (p : B256) (pair : Adr) : Mem :=
  ((((M.read 64 32).2.write p.toNat (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toBytes).write
      (p + 4).toNat pair.toB256.toBytes).read 64 32).2

/-- The reserve1 field (bits 112..223) of packed slot 8 as the literal code extracts it. -/
def skimReserve1Word (slot : B256) : B256 :=
  skimReserveMask &&& (slot / Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])

theorem skimSecondLine_inv {sevm : Sevm} {b final : Devm}
    {R : List B256} {M : Mem} {G : Nat} {p t1 t0 toWord : B256}
    (fork : CoveredFork sevm.benvStat.fork) (ptr : SkimPtr p M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : Line.Run sevm (St b (t1 :: t0 :: toWord :: R) M G) skimSecondLine final) :
    ∃ gas, final = St (afterSload sevm b 8)
      ((t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 :: (p + 36) ::
        0x70a08231 :: (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        skimReserve1Word (b.getStorVal sevm.currentTarget 8) :: 0x1a26 :: toWord :: t1 ::
        0x1aca :: t1 :: t0 :: toWord :: R)
      (skimRequestMemory M p sevm.currentTarget) gas := by
  have word0 : Bytes.toB256 (M.read 64 32).1 = p := ptr.2
  have p4 : (p + Bytes.toB256 [4]).toNat = p.toNat + 4 :=
    skimOffset (by change p.toNat + 4 < 2 ^ 256; omega)
  have word1 : Bytes.toB256 ((((M.read 64 32).2.write p.toNat (Bytes.toB256 [0x70, 0xa0, 0x82,
      0x31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0]).toBytes).write (p + Bytes.toB256 [4]).toNat sevm.currentTarget.toB256.toBytes).read 64
      32).1 = p :=
    (((ptr.extend 64 32).write p.toNat _ low).write (p + Bytes.toB256 [4]).toNat _
      (by rw [p4]; omega)).2
  dsimp only [skimSecondLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, word0] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  have hp := of_run_address hs
  have stack := hp.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have hd := St.of_stackRel hp
  rw [stack] at hd
  rw [hd] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, word1] at hd; subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_div hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨gas, rfl⟩ := ri_dup rfl hs
  cases run
  refine ⟨gas, ?_⟩
  rw [B256.sub_self]
  rfl

/-- Reading after a read's extension sees the same bytes. -/
theorem skimRead_extend (μ : Mem) (i n j m : Nat) : ((μ.read i n).2.read j m).1 = (μ.read j m).1 :=
  rfl

/-- The decoded balance word at the reply window of a moved query. -/
theorem skimReplyWord {Q : Mem} {p : B256} {out : Bytes} {pairs : List (Nat × Nat)}
    (wf : Mem.Wf Q) (long : 32 ≤ out.length) :
    Bytes.toB256 (((((Q.extends pairs).write p.toNat (out.take (32 : B256).toNat)).read
      64 32).2.read p.toNat 32).1) = Bytes.toB256 (out.take 32) := by
  have len : (out.take (32 : B256).toNat).length = 32 := by
    rw [List.length_take]; change min 32 out.length = 32; omega
  have image := Bytes.sliceD_writeAt Q.data.toList (out.take (32 : B256).toNat) p.toNat
  rw [len] at image
  rw [skimRead_extend, (((Mem.reads_data Q).extends pairs).write (wf.extends pairs) p.toNat
    (out.take (32 : B256).toNat)).read, image]
  rfl

theorem SkimPtr.extends {p : B256} {M : Mem} (h : SkimPtr p M) (pairs : List (Nat × Nat)) :
    SkimPtr p (M.extends pairs) := by
  refine ⟨h.1.extends pairs, ?_⟩
  rw [((Mem.reads_data M).extends pairs).read, ← (Mem.reads_data M).read]
  exact h.2

/-- The moved request keeps the free pointer. -/
theorem skimRequestMemory_ptr {M : Mem} {p : B256} {pair : Adr} (ptr : SkimPtr p M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256) :
    SkimPtr p (skimRequestMemory M p pair) := by
  have p4 : (p + 4).toNat = p.toNat + 4 := skimOffset (by change p.toNat + 4 < 2 ^ 256; omega)
  exact (((ptr.extend 64 32).write p.toNat _ low).write (p + 4).toNat _ (by rw [p4]; omega)).extend
    64 32

/-- The moved request's 36-byte window is exactly the source balanceOf calldata. -/
theorem skimRequestMemory_read {M : Mem} {p : B256} {pair : Adr} (wf : Mem.Wf M)
    (high : p.toNat + 1024 < 2 ^ 256) :
    ((skimRequestMemory M p pair).read p.toNat 36).1 =
      ExternalOperation.encode (.balanceOf pair) := by
  have p4 : (p + 4).toNat = p.toNat + 4 := skimOffset (by change p.toNat + 4 < 2 ^ 256; omega)
  have w1 := wf.extend 64 32
  have r2 := ((Mem.reads_data M).extend 64 32).write w1 p.toNat
    (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toBytes
  have r3 : Mem.Reads (skimRequestMemory M p pair) _ :=
    (r2.write (w1.write _ _) (p + 4).toNat pair.toB256.toBytes).extend 64 32
  rw [r3.read, p4, show (36 : Nat) = 4 + 32 from rfl, List.sliceD_split,
    Bytes.sliceD_writeAt_before _ _ p.toNat 4 (p.toNat + 4) (by omega),
    Bytes.sliceD_writeAt_inside _ _ p.toNat p.toNat 4 (by omega)
      (by rw [B256.length_toBytes]; omega), Nat.sub_self,
    show (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]).toBytes.sliceD 0 4 0 = [0x70, 0xa0, 0x82, 0x31] from
        by decide,
    ← B256.length_toBytes pair.toB256, Bytes.sliceD_writeAt]
  simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

/-- The literal unlock tail: two cache pops, SSTORE slot12 := 1, return-tag jump, STOP. -/
theorem skimUnlockTail_inv {D : Exec.Deriv} {sevm : Sevm} {d post : Devm}
    {R0 : List B256} {M : Mem} {G : Nat} {t1 t0 toWord tag : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St d (t1 :: t0 :: toWord :: tag :: R0) M G) t_1aca_c67 (.done (.halted post))) :
    ∃ M' g, post = St (afterSstore sevm d 12 1) R0 M' g := by
  unfold t_1aca_c67 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sstore fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  cases run with
  | jump _ _ lookup pop k =>
    change some t_0257_c73 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at k
    unfold t_0257_c73 at k
    obtain ⟨g, k⟩ := ric_destP k
    cases k with
    | last stop =>
      have eq := Except.ok.inj stop
      exact ⟨_, g, eq.symm⟩

/-- Facts of the second skim query, transfer1 and unlock from the post-transfer0 frame. -/
def SkimSecondFacts (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (M : Mem)
    (p t1 t0 toWord tag : B256) (R0 : List B256) (post : Devm) : Prop :=
    let W := afterSload sevm b 8
    let tm := t1 &&& 0xffffffffffffffffffffffffffffffffffffffff
    let r1 := skimReserve1Word (b.getStorVal sevm.currentTarget 8)
    let S := (p + 36) :: 0x70a08231 :: tm :: r1 :: 0x1a26 :: toWord :: t1 :: 0x1aca :: t1 ::
      t0 :: toWord :: tag :: R0
    (W.getCode tm.toAdr).size.toB256 ≠ 0 ∧
    ∃ (gw : B256) (callGas : Nat) (d1 : Devm) (out1 : Bytes),
      StepIn D sevm
        (St (temporalAccountAccessBase W tm.toAdr) (gw :: tm :: p :: 36 :: p :: 32 :: S)
          (skimRequestMemory M p sevm.currentTarget) callGas) (.exec .staticcall) d1 ∧
      StaticCallPost (temporalAccountAccessBase W tm.toAdr) d1 S
        (skimRequestMemory M p sevm.currentTarget) p 36 p 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      StaticAnswered sevm (temporalAccountAccessBase W tm.toAdr) tm.toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out1 ∧
      r1 ≤ Bytes.toB256 (out1.take 32) ∧
      ∃ (forwarded : B256) (callGas' : Nat) (V : Mem) (d2 : Devm),
        let a1 := Bytes.toB256 (out1.take 32) - r1
        StepIn D sevm (St d1 (forwarded ::
          (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 0 :: (64 + p + 100) :: 68 ::
          (64 + p + 100) :: 0 :: (68 + (64 + p + 100)) ::
          (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: a1 :: toWord :: t1 ::
          0x1aca :: t1 :: t0 :: toWord :: tag :: R0) V callGas') (.exec .call) d2 ∧
        (V.read (p.toNat + 164) 68).1 = abiSelectorBytes 0xa9059cbb ++
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ a1.toBytes ∧
        d2.output = d1.output ∧ d2.returnData.length < 2 ^ 256 ∧
        (d2.returnData = [] ∨ (32 ≤ d2.returnData.length ∧
          Bytes.toB256 (d2.returnData.sliceD 0 32 0) ≠ 0)) ∧
        ∃ M' residual, post = St (afterSstore sevm d2 12 1) R0 M' residual

/-- The second skim query, transfer1 and unlock from the cached frame after transfer0, at
a fitting moved free pointer `p`. The reserve1 field is read on the post-transfer0 world. -/
theorem skimSecondHalf_inv {D : Exec.Deriv} {sevm : Sevm} {b post : Devm}
    {R0 : List B256} {M : Mem} {G : Nat} {p t1 t0 toWord tag : B256}
    (fork : CoveredFork sevm.benvStat.fork) (ptr : SkimPtr p M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (t1 :: t0 :: toWord :: tag :: R0) M G) t_1a2b_c34 (.done (.halted post))) :
    SkimSecondFacts D sevm b M p t1 t0 toWord tag R0 post := by
  unfold SkimSecondFacts
  dsimp only
  have h := run
  unfold t_1a2b_c34 at h
  obtain ⟨_, h⟩ := ric_destP h
  change SFunc.RunCutP (StepIn D) cert.prog sevm [] _
    (skimSecondLine.foldr SFunc.next
      (syncCodeGuardLine.foldr SFunc.next (.next (.push [0x19, 0xee] (by decide))
        (.branchTo t_1ac6_c34 67)))) _ at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => StepIn.toRun step) skimSecondLine h
  obtain ⟨_, state⟩ := skimSecondLine_inv fork ptr low high line
  rw [state] at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => StepIn.toRun step) syncCodeGuardLine h
  obtain ⟨_, state⟩ := syncCodeGuardLine_inv fork line
  rw [state] at h
  obtain ⟨_, hs, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  cases h with
  | toZero _ pop k =>
    obtain ⟨_, _, eq⟩ := St.of_pop2 pop
    rw [eq] at k
    exact (k.false_of_noOk (by decide : t_1ac6_c34.noOk = true)).elim
  | toSucc _ w nonzero _ lookup pop k =>
    change some t_19ee_c67 = _ at lookup
    cases lookup
    obtain ⟨_, hw, eq⟩ := St.of_pop2 pop
    rw [eq] at k
    rw [← hw] at nonzero
    have zero := eq_zero_of_iszero_ne_zero nonzero
    have codeNonzero : ((afterSload sevm b 8).getCode
        (t1 &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).size.toB256 ≠ 0 := by
      intro hz
      rw [hz, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    rw [zero] at k
    obtain ⟨gw, callGas, d1, out1, _, call, post1, bound, answered, k⟩ :=
      staticCallGuard_invP [0x1a, 0x02] (by decide) rfl StepIn.toRun fork (by decide) k
    rw [show (36 : B256).toNat = 36 from rfl,
      skimRequestMemory_read ptr.1 high] at answered
    have pR1 : SkimPtr p ((((skimRequestMemory M p sevm.currentTarget).extends
        [(p.toNat, (36 : B256).toNat), (p.toNat, (32 : B256).toNat)]).write p.toNat
          (out1.take (32 : B256).toNat))) :=
      ((skimRequestMemory_ptr ptr low high).extends _).write p.toNat _ low
    have rR1 := (((Mem.reads_data (skimRequestMemory M p sevm.currentTarget)).extends
        [(p.toNat, (36 : B256).toNat), (p.toNat, (32 : B256).toNat)]).write
          ((skimRequestMemory_ptr ptr low high).1.extends _) p.toNat
          (out1.take (32 : B256).toNat))
    unfold t_1a02_c67 at k
    obtain ⟨_, k⟩ := ric_destP k
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨d, hs, k⟩ := ric_nextP k
    obtain ⟨_, hd⟩ := ri_mload (StepIn.toRun hs)
    rw [show (Bytes.toB256 [64]).toNat = 64 from by decide, pR1.2] at hd
    subst d
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_returndatasize (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    rcases ric_branchP k with ⟨_, _, failed⟩ | ⟨accepted, _, k⟩
    · exact (failed.false_of_noOk (by decide : t_1a14_c67.noOk = true)).elim
    have full : d1.returnData.length < 2 ^ 256 := by rw [post1.returnData]; exact bound
    have width := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero accepted)
    rw [B256.toNat_toB256_of_lt full, post1.returnData] at width
    change 32 ≤ out1.length at width
    have word1 := skimReplyWord (Q := skimRequestMemory M p sevm.currentTarget) (p := p)
      (pairs := [(p.toNat, (36 : B256).toNat), (p.toNat, (32 : B256).toNat)])
      (skimRequestMemory_ptr ptr low high).1 width
    unfold t_1a18_c67 at k
    obtain ⟨_, k⟩ := ric_destP k
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
    obtain ⟨d, hs, k⟩ := ric_nextP k
    obtain ⟨_, hd⟩ := ri_mload (StepIn.toRun hs)
    rw [word1] at hd
    subst d
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, k⟩ := ric_nextP k; obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun hs)
    rw [show Bytes.toB256 [0x22,0x6e] &&& Bytes.toB256 [0xff,0xff,0xff,0xff] = (0x226e : B256)
      from by decide] at k
    cases k with
    | callHalt d lookup pop callee =>
        change some t_226e_c59 = _ at lookup
        cases lookup
        have checked := (St.of_pop1 pop).2 ▸ callee
        obtain ⟨_, _, returned⟩ := sub59_inv (checked.mono StepIn.toRun)
        cases returned
    | callRet d lookup pop callee body =>
      change some t_226e_c59 = _ at lookup
      cases lookup
      have checked := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨cover, _, returned⟩ := sub59_inv (checked.mono StepIn.toRun)
      cases returned
      unfold t_1a26_c67 at body
      obtain ⟨_, body⟩ := ric_destP body
      obtain ⟨_, hs, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
      cases body with
      | callHalt d lookup pop callee =>
          change some t_1fdb_c57 = _ at lookup
          cases lookup
          exact False.elim (callee.not_halted_entry (S := [16,17,57,71])
            (by decide) (by decide : 57 ∈ [16,17,57,71]) (by rfl : cert.prog[57]? = some t_1fdb_c57) rfl)
      | callRet out lookup pop callee tail =>
          change some t_1fdb_c57 = _ at lookup
          cases lookup
          have helper := (St.of_pop1 pop).2 ▸ callee
          have pM3 := (pR1.extend 64 32).extend p.toNat 32
          obtain ⟨forwarded, callGas', V, d2, call2, calldata, output, width2, accepted2,
            M', residual, outEq⟩ := skimTransfer_inv StepIn.toRun fork pM3.1 pM3.2 low high helper
          rw [outEq] at tail
          obtain ⟨M'', g, final⟩ := skimUnlockTail_inv fork tail
          exact ⟨codeNonzero, gw, callGas, d1, out1, call, post1, width, bound, answered, cover,
            forwarded, callGas', V, d2, call2, calldata, output, width2, accepted2, M'', g, final⟩

/-- The free pointer left by transfer0's helper: 292 for an empty reply, else the modular bump. -/
def skimFirstPointer (reply : Bytes) : B256 :=
  if reply = [] then 292 else 292 + ((reply.length.toB256 + 63) &&& ~~~31)

/-- Any reply below 2^128 bytes leaves a fitting pointer (no modular wrap). -/
theorem skimFirstPointer_fit {reply : Bytes} (short : reply.length < 2 ^ 128) :
    96 ≤ (skimFirstPointer reply).toNat ∧ (skimFirstPointer reply).toNat + 1024 < 2 ^ 256 := by
  unfold skimFirstPointer
  by_cases empty : reply = []
  · rw [ite_eq_left empty]
    exact ⟨by decide, by decide⟩
  · rw [ite_eq_right empty]
    have lenNat : reply.length.toB256.toNat = reply.length :=
      B256.toNat_toB256_of_lt (by omega)
    have sum : (reply.length.toB256 + 63).toNat = reply.length + 63 := by
      rw [skimOffset (by rw [lenNat]; change reply.length + 63 < 2 ^ 256; omega), lenNat]; rfl
    have masked : ((reply.length.toB256 + 63) &&& ~~~(31 : B256)).toNat ≤ reply.length + 63 := by
      rw [B256.toNat_and, sum]
      exact Nat.and_le_left
    have total : (292 + ((reply.length.toB256 + 63) &&& ~~~31)).toNat =
        292 + ((reply.length.toB256 + 63) &&& ~~~(31 : B256)).toNat :=
      skimOffset (by change 292 + _ < 2 ^ 256; omega)
    rw [total]
    exact ⟨by omega, by omega⟩

/-- Every successful raw skim run at the Pair code: the public guards (value zero, ABI
head, unlocked, nonstatic), the four own external calls in order with their requests,
full replies and decoded words, both checked surpluses, both transfer acceptances, and
the final unlock store. The second half is stated for a fitting transfer0 reply pointer
(`skimFirstPointer_fit` discharges it for every reply below 2^128 bytes). -/
theorem skim_raw_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let D : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (32 : B256) ≤ sevm.data.length.toB256 - 4 ∧ b.getStorVal sevm.currentTarget 12 = 1 ∧
      SkimFirstFacts D sevm b [0x0257, 0xbc25cf77] getterInitMemory
        (skimToWord sevm) (fun d Mres _ =>
          96 ≤ (skimFirstPointer d.returnData).toNat →
          (skimFirstPointer d.returnData).toNat + 1024 < 2 ^ 256 →
          SkimSecondFacts D sevm d Mres (skimFirstPointer d.returnData)
            (skimToken1 sevm b) (skimToken0 sevm b)
            (skimToWord sevm) 0x0257 [0xbc25cf77] post) := by
  intro D
  obtain ⟨f, entry, run'⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, guarded⟩ := syncGuards_inv run'
  have h := SFunc.runP_iff_runCutP_nil.mp guarded
  obtain ⟨_, h⟩ := skimSelector_inv selector h
  obtain ⟨abi, _, h⟩ := skimWrapper_inv h
  obtain ⟨unlocked, _, h⟩ := skimLock_inv fork h
  refine ⟨value, size, abi, unlocked, ?_⟩
  refine (skimFirstHalf_inv fork getterInitMemory_ptr h).mono ?_
  intro out0 d Mres g memory hM tail low high
  have reply := balanceReplyMemory_ptr out0
    (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)
  have ptr := skimAfterFirst_ptr (a0 := Bytes.toB256 (out0.take 32) -
    skimReserve0 sevm b) (toWord := skimToWord sevm)
    (reply := d.returnData) reply
  rw [← memory, ← hM] at ptr
  exact skimSecondHalf_inv fork (p := skimFirstPointer d.returnData) ptr low high tail

end Blanc.Lift.UniswapV2Pair
