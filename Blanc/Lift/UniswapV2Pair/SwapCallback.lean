import Blanc.Lift.UniswapV2Pair.SwapTransfer
import Blanc.Lift.MutableCallPost

/-! The swap's conditional `uniswapV2Call` callback (`t_08e1_c4..t_09c3_c5`). -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The callback calldata image after the body's eight ordered memory writes at pointer `n`:
the selector word, the four head words and the length, the copied data and one zero word. -/
def swapCallbackImage (bs : Bytes) (n : Nat) (w0 c a0 a1 lw : B256) (data : Bytes) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
    (Bytes.writeAt (Bytes.writeAt bs n w0.toBytes) (n + 4) c.toBytes) (n + 36) a0.toBytes)
    (n + 68) a1.toBytes) (n + 100) (128 : B256).toBytes) (n + 132) lw.toBytes) (n + 164) data)
    (n + 164 + data.length) (0 : B256).toBytes

/-- The CALL input window of the callback is exactly the selector, the head words, the data and
the zero padding to a word boundary. -/
theorem swapCallbackImage_window (bs : Bytes) (n : Nat) (w0 c a0 a1 lw : B256) (data : Bytes) :
    (swapCallbackImage bs n w0 c a0 a1 lw data).sliceD n
        (164 + data.length + (32 - data.length % 32) % 32) 0 =
      w0.toBytes.take 4 ++ (c.toBytes ++ a0.toBytes ++ a1.toBytes ++ (128 : B256).toBytes ++
        lw.toBytes) ++ data ++ List.replicate ((32 - data.length % 32) % 32) 0 := by
  let X := swapCallbackImage bs n w0 c a0 a1 lw data
  let len := data.length
  let pad := (32 - len % 32) % 32
  have padLe : pad ≤ 32 := by omega
  have lw32 := B256.length_toBytes (0 : B256)
  have p0 : X.sliceD n 4 0 = w0.toBytes.take 4 := by
    simp only [X, swapCallbackImage]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_inside _ _ _ _ _ (Nat.le_refl _) (by rw [B256.length_toBytes]; omega),
      Nat.sub_self]
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ (by rw [B256.length_toBytes]; omega)]
  have p1 : X.sliceD (n + 4) 32 0 = c.toBytes := by
    simp only [X, swapCallbackImage]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      sliceD_word_same]
  have p2 : X.sliceD (n + 4 + 32) 32 0 = a0.toBytes := by
    simp only [X, swapCallbackImage]
    rw [show n + 4 + 32 = n + 36 by omega]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_same]
  have p3 : X.sliceD (n + 4 + 32 + 32) 32 0 = a1.toBytes := by
    simp only [X, swapCallbackImage]
    rw [show n + 4 + 32 + 32 = n + 68 by omega]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      sliceD_word_same]
  have p4 : X.sliceD (n + 4 + 32 + 32 + 32) 32 0 = (128 : B256).toBytes := by
    simp only [X, swapCallbackImage]
    rw [show n + 4 + 32 + 32 + 32 = n + 100 by omega]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), sliceD_word_same]
  have p5 : X.sliceD (n + 4 + 32 + 32 + 32 + 32) 32 0 = lw.toBytes := by
    simp only [X, swapCallbackImage]
    rw [show n + 4 + 32 + 32 + 32 + 32 = n + 132 by omega]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      sliceD_word_same]
  have p6 : X.sliceD (n + 4 + 32 + 32 + 32 + 32 + 32) len 0 = data := by
    simp only [X, swapCallbackImage]
    rw [show n + 4 + 32 + 32 + 32 + 32 + 32 = n + 164 by omega]
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), Bytes.sliceD_writeAt]
  have p7 : X.sliceD (n + 4 + 32 + 32 + 32 + 32 + 32 + len) pad 0 = List.replicate pad 0 := by
    simp only [X, swapCallbackImage]
    rw [show n + 4 + 32 + 32 + 32 + 32 + 32 + len = n + 164 + data.length by omega]
    rw [Bytes.sliceD_writeAt_inside _ _ _ _ _ (Nat.le_refl _) (by rw [lw32]; omega), Nat.sub_self,
      show (0 : B256).toBytes = List.replicate 32 0 from rfl]
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ (by rw [List.length_replicate]; omega),
      List.take_replicate, Nat.min_eq_left padLe]
  rw [show 164 + data.length + (32 - data.length % 32) % 32 =
      4 + (32 + (32 + (32 + (32 + (32 + (len + pad)))))) by omega,
    List.sliceD_split _ _ 4, List.sliceD_split _ _ 32, List.sliceD_split _ _ 32,
    List.sliceD_split _ _ 32, List.sliceD_split _ _ 32, List.sliceD_split _ _ 32,
    List.sliceD_split _ _ len]
  change X.sliceD n 4 0 ++ (X.sliceD (n + 4) 32 0 ++ (X.sliceD (n + 4 + 32) 32 0 ++
    (X.sliceD (n + 4 + 32 + 32) 32 0 ++ (X.sliceD (n + 4 + 32 + 32 + 32) 32 0 ++
    (X.sliceD (n + 4 + 32 + 32 + 32 + 32) 32 0 ++ (X.sliceD (n + 4 + 32 + 32 + 32 + 32 + 32) len 0 ++
    X.sliceD (n + 4 + 32 + 32 + 32 + 32 + 32 + len) pad 0)))))) = _
  rw [p0, p1, p2, p3, p4, p5, p6, p7]
  simp only [List.append_assoc]
  rfl

/-- The callback selector word the body stores at the free pointer. -/
def swapCallbackSelectorWord : B256 :=
  0x10d1e85c00000000000000000000000000000000000000000000000000000000

/-- The body's eight ordered callback-calldata writes at pointer `n`. -/
def swapCallbackMem (M : Mem) (n : Nat) (w0 c a0 a1 lw : B256) (data : Bytes) : Mem :=
  (((((((M.write n w0.toBytes).write (n + 4) c.toBytes).write (n + 36) a0.toBytes).write
    (n + 68) a1.toBytes).write (n + 100) (128 : B256).toBytes).write (n + 132) lw.toBytes).write
    (n + 164) data).write (n + 164 + data.length) (0 : B256).toBytes

theorem swapCallbackMem_read {M : Mem} (wf : Mem.Wf M) (n : Nat) (w0 c a0 a1 lw : B256)
    (data : Bytes) (i k : Nat) :
    ((swapCallbackMem M n w0 c a0 a1 lw data).read i k).1 =
      (swapCallbackImage M.data.toList n w0 c a0 a1 lw data).sliceD i k 0 := by
  have r0 := Mem.reads_data M
  have wf1 := wf.write n w0.toBytes
  have wf2 := wf1.write (n + 4) c.toBytes
  have wf3 := wf2.write (n + 36) a0.toBytes
  have wf4 := wf3.write (n + 68) a1.toBytes
  have wf5 := wf4.write (n + 100) (128 : B256).toBytes
  have wf6 := wf5.write (n + 132) lw.toBytes
  have wf7 := wf6.write (n + 164) data
  have r8 := ((((((((r0.write wf n w0.toBytes).write wf1 (n + 4) c.toBytes).write wf2
    (n + 36) a0.toBytes).write wf3 (n + 68) a1.toBytes).write wf4 (n + 100)
    (128 : B256).toBytes).write wf5 (n + 132) lw.toBytes).write wf6 (n + 164) data).write wf7
    (n + 164 + data.length) (0 : B256).toBytes)
  exact r8.read i k

theorem swapCallbackMem_ptr {p : B256} {m : Nat} {M : Mem} (mem : PtrMem p m M) {n : Nat}
    (lower : 96 ≤ n) (w0 c a0 a1 lw : B256) (data : Bytes) :
    ∃ m', PtrMem p m' (swapCallbackMem M n w0 c a0 a1 lw data) :=
  ⟨_, ((((((((mem.write_bytes n w0.toBytes (Or.inr lower)).write_bytes (n + 4) c.toBytes
    (Or.inr (by omega))).write_bytes (n + 36) a0.toBytes (Or.inr (by omega))).write_bytes
    (n + 68) a1.toBytes (Or.inr (by omega))).write_bytes (n + 100) (128 : B256).toBytes
    (Or.inr (by omega))).write_bytes (n + 132) lw.toBytes (Or.inr (by omega))).write_bytes
    (n + 164) data (Or.inr (by omega))).write_bytes (n + 164 + data.length) (0 : B256).toBytes
    (Or.inr (by omega)))⟩

/-- The CALL window is the model's `uniswapV2Call` request calldata. -/
theorem swapCallbackMem_calldata {M : Mem} (wf : Mem.Wf M) (n : Nat) (caller : Adr)
    (a0 a1 : B256) (data : Bytes) :
    ((swapCallbackMem M n swapCallbackSelectorWord caller.toB256 a0 a1 (Nat.toB256 data.length)
      data).read n (164 + data.length + (32 - data.length % 32) % 32)).1 =
      ExternalOperation.encode (.callback caller a0 a1 data) := by
  rw [swapCallbackMem_read wf, swapCallbackImage_window,
    show swapCallbackSelectorWord.toBytes.take 4 = [0x10, 0xd1, 0xe8, 0x5c] from by decide]
  simp only [ExternalOperation.encode, encodeWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-- The end of the callback calldata area, as the body computes it. -/
def swapCallbackEnd (q len : B256) : B256 :=
  32 + (32 + (32 + (32 + (32 + (4 + q))))) + (len + 31 &&& ~~~31)

/-- The actual callback CALL: the recipient has code, the CALL's input window is the model's
`uniswapV2Call` calldata with the actual variable data, and its flag is set. -/
def SwapCallbackCall (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (L : List B256) (M : Mem)
    (q toWord a0 a1 len start : B256) (d : Devm) : Prop :=
  let target := (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord
  let data := sevm.data.sliceD start.toNat len.toNat 0
  let Mcb := swapCallbackMem M q.toNat swapCallbackSelectorWord sevm.caller.toB256 a0 a1 len data
  let insize := swapCallbackEnd q len - q
  (b.getCode target.toAdr).size.toB256 ≠ 0 ∧
  (∃ gas callGas, StepIn D sevm (St (temporalAccountAccessBase b target.toAdr)
    (gas :: target :: 0 :: q :: insize :: q :: 0 :: swapCallbackEnd q len :: 0x10d1e85c :: target :: L)
    Mcb callGas) (.exec .call) d) ∧
  (Mcb.read q.toNat insize.toNat).1 = ExternalOperation.encode (.callback sevm.caller a0 a1 data) ∧
  ∃ flag, flag ≠ 0 ∧ MutableCallPost (temporalAccountAccessBase b target.toAdr) d
    (swapCallbackEnd q len :: 0x10d1e85c :: target :: L) Mcb q insize q 0 flag

private theorem swapExtends2 (M : Mem) (i1 s1 i2 s2 : Nat) (rd : Bytes) :
    (M.extends [(i1, s1), (i2, s2)]).write i2 (rd.take 0) = ((M.read i1 s1).2.read i2 s2).2 := by
  rw [List.take_zero]
  rfl

/-- Literal callback calldata preparation, shared by the old inverse and actual cursor. -/
def swapCallbackPrepareLine : List Ninst := [
  .reg (.dup 8),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .push [0x10, 0xd1, 0xe8, 0x5c] (by decide),
  .reg .caller,
  .reg (.dup 13),
  .reg (.dup 13),
  .reg (.dup 12),
  .reg (.dup 12),
  .push [0x40] (by decide),
  .reg .mload,
  .reg (.dup 6),
  .push [0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .push [0xe0] (by decide),
  .reg .shl,
  .reg (.dup 1),
  .reg .mstore,
  .push [0x04] (by decide),
  .reg .add,
  .reg (.dup 0),
  .reg (.dup 6),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .reg (.dup 1),
  .reg .mstore,
  .push [0x20] (by decide),
  .reg .add,
  .reg (.dup 5),
  .reg (.dup 1),
  .reg .mstore,
  .push [0x20] (by decide),
  .reg .add,
  .reg (.dup 4),
  .reg (.dup 1),
  .reg .mstore,
  .push [0x20] (by decide),
  .reg .add,
  .reg (.dup 0),
  .push [0x20] (by decide),
  .reg .add,
  .reg (.dup 2),
  .reg (.dup 1),
  .reg .sub,
  .reg (.dup 2),
  .reg .mstore,
  .reg (.dup 4),
  .reg (.dup 4),
  .reg (.dup 2),
  .reg (.dup 1),
  .reg (.dup 1),
  .reg .mstore,
  .push [0x20] (by decide),
  .reg .add,
  .reg (.swap 2),
  .reg .pop,
  .reg (.dup 0),
  .reg (.dup 2),
  .reg (.dup 4),
  .reg .calldatacopy,
  .push [0x00] (by decide),
  .reg (.dup 1),
  .reg (.dup 4),
  .reg .add,
  .reg .mstore,
  .push [0x1f] (by decide),
  .reg .not,
  .push [0x1f] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .and,
  .reg (.swap 0),
  .reg .pop,
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .add,
  .reg (.swap 2),
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg (.swap 6),
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .push [0x00] (by decide),
  .push [0x40] (by decide),
  .reg .mload,
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .sub,
  .reg (.dup 1),
  .push [0x00] (by decide),
  .reg (.dup 7),
  .reg (.dup 0)
]

theorem swapCallbackPrepareLine_inv {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {G n : Nat} {q t1 t0 r1 r0 len start toWord a1 a0 rho : B256}
    (mem : PtrMem q n M) (lower : 128 ≤ q.toNat) (upper : q.toNat < 2 ^ 162)
    (short : len.toNat ≤ 2 ^ 32)
    (run : Line.Run sevm (St b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: R)
      M G) swapCallbackPrepareLine d) :
    ∃ gas, d = St b
      ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) ::
        (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) :: 0 :: q ::
        (swapCallbackEnd q len - q) :: q :: 0 :: swapCallbackEnd q len ::
        0x10d1e85c :: (0xffffffffffffffffffffffffffffffffffffffff &&& toWord) ::
        t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: R)
      (swapCallbackMem M q.toNat swapCallbackSelectorWord sevm.caller.toB256 a0 a1 len
        (sevm.data.sliceD start.toNat len.toNat 0)) gas := by
  have read0 : Bytes.toB256 (M.read 64 32).1 = q := mem.word
  have same0 : (M.read 64 32).2 = M := mem.read_self (by have := mem.ge; omega)
  dsimp only [swapCallbackPrepareLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_caller hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, eq⟩ := ri_mload hs
  rw [show (Bytes.toB256 [64]).toNat = 64 from rfl, read0, same0] at eq
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_shl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_calldatacopy hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_not hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  dsimp only [List.set] at run
  have vcaller : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& sevm.caller.toB256) =
      sevm.caller.toB256 := by
    have h := ff20_and_word sevm.caller.toB256
    rw [toAdr_toB256] at h
    change Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255] &&& (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& _) = _
    rw [h, h]
  have vsel : (Bytes.toB256 [255, 255, 255, 255] &&& Bytes.toB256 [16, 209, 232, 92]) <<<
      (Bytes.toB256 [224]).toNat = swapCallbackSelectorWord := by decide
  simp only [vsel, show Bytes.toB256 [32] = (32 : B256) from rfl, show Bytes.toB256 [4] = (4 : B256) from rfl,
    show Bytes.toB256 [0] = (0 : B256) from rfl, show Bytes.toB256 [31] = (31 : B256) from rfl,
    show Bytes.toB256 [64] = (64 : B256) from rfl,
    show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255] = (0xffffffffffffffffffffffffffffffffffffffff : B256) from rfl] at run
  simp only [vcaller] at run
  let data := List.sliceD sevm.data start.toNat len.toNat 0
  have dataLen : data.length = len.toNat := List.length_sliceD _ _ _ _
  have a4 : (4 + q).toNat = q.toNat + 4 := by
    rw [B256.toNat_add, show (4 : B256).toNat = 4 from rfl, Nat.lo_eq_of_lt (by omega), Nat.add_comm]
  have a36 : (32 + (4 + q)).toNat = q.toNat + 36 := by
    rw [B256.toNat_add, a4, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a68 : (32 + (32 + (4 + q))).toNat = q.toNat + 68 := by
    rw [B256.toNat_add, a36, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a100 : (32 + (32 + (32 + (4 + q)))).toNat = q.toNat + 100 := by
    rw [B256.toNat_add, a68, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a132 : (32 + (32 + (32 + (32 + (4 + q))))).toNat = q.toNat + 132 := by
    rw [B256.toNat_add, a100, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a164 : (32 + (32 + (32 + (32 + (32 + (4 + q)))))).toNat = q.toNat + 164 := by
    rw [B256.toNat_add, a132, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have aend : (32 + (32 + (32 + (32 + (32 + (4 + q))))) + len).toNat = q.toNat + 164 + data.length := by
    rw [B256.toNat_add, a164, dataLen, Nat.lo_eq_of_lt (by omega)]
  have v128 : 32 + (32 + (32 + (32 + (4 + q)))) - (4 + q) = (128 : B256) := by
    apply B256.toNat_inj
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat (by rw [a132, a4]; omega)), a132, a4,
      show (128 : B256).toNat = 128 from rfl]
    omega
  simp only [a4, a36, a68, a100, a132, a164, aend, v128] at run
  rw [← swapCallbackMem.eq_1 M q.toNat swapCallbackSelectorWord sevm.caller.toB256 a0 a1 len data] at run
  obtain ⟨m', mcb⟩ := swapCallbackMem_ptr mem (by omega : 96 ≤ q.toNat) swapCallbackSelectorWord
    sevm.caller.toB256 a0 a1 len data
  have read1 : Bytes.toB256 ((swapCallbackMem M q.toNat swapCallbackSelectorWord sevm.caller.toB256
      a0 a1 len data).read 64 32).1 = q := mcb.word
  have same1 := mcb.read_self (by have := mcb.ge; omega : 64 + 32 ≤ m')
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, eq⟩ := ri_mload hs
  rw [show (64 : B256).toNat = 64 from rfl, read1, same1] at eq
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  cases run
  exact ⟨_, rfl⟩

/-- Literal branch on callback data length. -/
def swapCallbackGuardLine : List Ninst :=
  [.reg (.dup 6), .reg .iszero, .push [0x09,0xc3] (by decide)]

theorem swapCallbackGuardLine_inv {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {G : Nat} {t1 t0 r1 r0 len start toWord a1 a0 rho : B256}
    (line : Line.Run sevm (St b
      (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: R)
      M G) swapCallbackGuardLine d) :
    ∃ gas, d = St b (0x9c3 :: B256.eqCheck len 0 ::
      t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: R) M gas := by
  dsimp only [swapCallbackGuardLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  exact ⟨gas, state⟩

/-- The callback drops its CALL operands at the checked success join. -/
def swapCallbackReturnLine : List Ninst := [.reg .pop, .reg .pop, .reg .pop, .reg .pop]

theorem swapCallbackReturnLine_inv {sevm : Sevm} {b d : Devm} {L : List B256}
    {M : Mem} {G : Nat} {a x y z : B256}
    (line : Line.Run sevm (St b (a :: x :: y :: z :: L) M G) swapCallbackReturnLine d) :
    ∃ gas, d = St b L M gas := by
  dsimp only [swapCallbackReturnLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_pop step
  cases line
  exact ⟨gas, state⟩

/-- The actual callback input window has its natural, nonwrapping size. -/
theorem swapCallbackEnd_layout {q len : B256}
    (upper : q.toNat < 2 ^ 162) (short : len.toNat ≤ 2 ^ 32) :
    (swapCallbackEnd q len).toNat = q.toNat + 164 + 32 * ((len.toNat + 31) / 32) ∧
    (swapCallbackEnd q len - q).toNat = 164 + len.toNat + (32 - len.toNat % 32) % 32 := by
  have a4 : (4 + q).toNat = q.toNat + 4 := by
    rw [B256.toNat_add, show (4 : B256).toNat = 4 from rfl, Nat.lo_eq_of_lt (by omega), Nat.add_comm]
  have a36 : (32 + (4 + q)).toNat = q.toNat + 36 := by
    rw [B256.toNat_add, a4, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a68 : (32 + (32 + (4 + q))).toNat = q.toNat + 68 := by
    rw [B256.toNat_add, a36, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a100 : (32 + (32 + (32 + (4 + q)))).toNat = q.toNat + 100 := by
    rw [B256.toNat_add, a68, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a132 : (32 + (32 + (32 + (32 + (4 + q))))).toNat = q.toNat + 132 := by
    rw [B256.toNat_add, a100, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have a164 : (32 + (32 + (32 + (32 + (32 + (4 + q)))))).toNat = q.toNat + 164 := by
    rw [B256.toNat_add, a132, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have mask32 : ((len + 31 &&& ~~~31 : B256)).toNat = 32 * ((len.toNat + 31) / 32) := by
    have sumNat : (len + (31 : B256)).toNat = len.toNat + 31 := by
      rw [B256.toNat_add, show (31 : B256).toNat = 31 from rfl, Nat.lo_eq_of_lt (by omega)]
    rw [B256.toNat_and, sumNat, show (~~~ (31 : B256)).toNat = 2 ^ 256 - 32 from rfl,
      Nat.and_mask32 (by omega)]
  have endNat : (swapCallbackEnd q len).toNat = q.toNat + 164 + 32 * ((len.toNat + 31) / 32) := by
    unfold swapCallbackEnd
    rw [B256.toNat_add, a164, mask32, Nat.lo_eq_of_lt (by omega)]
  have insizeNat : (swapCallbackEnd q len - q).toNat = 164 + len.toNat + (32 - len.toNat % 32) % 32 := by
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_of_toNat_le_toNat (by rw [endNat]; omega)), endNat]
    omega
  exact ⟨endNat, insizeNat⟩

/-- The callback build, code check, CALL and success test, from `t_08e8_c4` to the join. -/
theorem swapCallbackCall_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {n : Nat} {q t1 t0 r1 r0 len start toWord a1 a0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem q n M)
    (lower : 128 ≤ q.toNat) (upper : q.toNat < 2 ^ 162) (short : len.toNat ≤ 2 ^ 32)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G)
      t_08e8_c4 seg) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R
    ∃ d gas, SwapCallbackCall D sevm b L M q toWord a0 a1 len start d ∧
      (∃ m', PtrMem q m' d.memory) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm [] (St d L d.memory gas) t_09c3_c5 seg := by
  intro L
  unfold t_08e8_c4 at run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapCallbackPrepareLine run
  obtain ⟨_, rfl⟩ := swapCallbackPrepareLine_inv mem lower upper short line
  let data := List.sliceD sevm.data start.toNat len.toNat 0
  have dataLen : data.length = len.toNat := List.length_sliceD _ _ _ _
  obtain ⟨m', mcb⟩ := swapCallbackMem_ptr mem (by omega : 96 ≤ q.toNat) swapCallbackSelectorWord
    sevm.caller.toB256 a0 a1 len data
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_extcodesize fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨codeNz, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_09a6_c4.noOk = true))
  unfold t_09aa_c4 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, _, rfl⟩ := ri_gas (StepIn.toRun hs)
  obtain ⟨d, call, run⟩ := ric_nextP run
  obtain ⟨flag, post⟩ := ri_call_post fork (StepIn.toRun call)
  rw [St.self post.stack rfl] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨flagNz, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_09b5_c4.noOk = true))
  unfold t_09be_c4 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d', line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapCallbackReturnLine run
  obtain ⟨_, rfl⟩ := swapCallbackReturnLine_inv line
  have flag0 : flag ≠ 0 := by
    intro h
    rw [h] at flagNz
    exact flagNz (by decide)
  have code0 : (b.getCode ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toAdr).size.toB256 ≠ 0 := by
    intro h
    rw [h] at codeNz
    exact codeNz (by decide)
  obtain ⟨endNat, insize⟩ := swapCallbackEnd_layout upper short
  have insizeNat : (swapCallbackEnd q len - q).toNat =
      164 + data.length + (32 - data.length % 32) % 32 := by
    rw [dataLen]
    exact insize
  have calldata := swapCallbackMem_calldata mem.wf q.toNat sevm.caller a0 a1 data
  rw [show Nat.toB256 data.length = len by rw [dataLen, toB256_toNat]] at calldata
  have settled := post.settled flag0
  refine ⟨d, _, ⟨code0, ⟨_, _, call⟩, by rw [insizeNat]; exact calldata, flag, flag0, post⟩,
    ?_, run⟩
  rw [settled.1, show (0 : B256).toNat = 0 from rfl, swapExtends2]
  exact ⟨_, (mcb.extend _ _).extend _ _⟩

/-- The conditional callback as actually executed: empty data skips it and keeps world and
memory; nonempty data makes the actual callback CALL. -/
def SwapCallbackOpt (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (L : List B256) (M : Mem)
    (q toWord a0 a1 len start : B256) (b' : Devm) (M' : Mem) : Prop :=
  (len = 0 ∧ b' = b ∧ M' = M) ∨
  (len ≠ 0 ∧ SwapCallbackCall D sevm b L M q toWord a0 a1 len start b' ∧ M' = b'.memory)

/-- From the callback branch `t_08e1_c4` to the join `t_09c3_c5`, in both arms. -/
theorem swapCallback_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {n : Nat} {q t1 t0 r1 r0 len start toWord a1 a0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem q n M)
    (lower : 128 ≤ q.toNat) (upper : q.toNat < 2 ^ 162) (short : len.toNat ≤ 2 ^ 32)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G)
      t_08e1_c4 seg) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R
    ∃ (b' : Devm) (M' : Mem) (m' gas : Nat), SwapCallbackOpt D sevm b L M q toWord a0 a1 len start b' M' ∧
      PtrMem q m' M' ∧ SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b' L M' gas) t_09c3_c5 seg := by
  intro L
  unfold t_08e1_c4 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapCallbackGuardLine run
  obtain ⟨_, rfl⟩ := swapCallbackGuardLine_inv line
  rcases ric_branchToP (by intro bad; cases bad) (rfl : cert.prog[5]? = some t_09c3_c5) run with
    ⟨zero, _, run⟩ | ⟨skip, gas, run⟩
  · have nonzero : len ≠ 0 := by
      intro h
      rw [h] at zero
      exact absurd zero (by decide)
    obtain ⟨d, gas, call, ⟨m', ptr⟩, cont⟩ := swapCallbackCall_inv fork mem lower upper short run
    exact ⟨d, d.memory, m', gas, Or.inr ⟨nonzero, call, rfl⟩, ptr, cont⟩
  · exact ⟨b, M, n, gas, Or.inl ⟨eq_zero_of_iszero_ne_zero skip, rfl, rfl⟩, mem, run⟩

end Blanc.Lift.UniswapV2Pair
