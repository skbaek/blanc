import Blanc.Lift.UniswapV2Pair.SyncWalk

/-! The literal public swap entry: PC0 guards, the selector dispatch, and the ABI wrapper
`t_01be..t_024c` decoding `swap(uint256,uint256,address,bytes)`. The dynamic `bytes data`
argument is a calldata slice (`bytes calldata`): the wrapper validates its offset and length
and passes their calldata position on the stack; it copies nothing into memory, so the free
pointer at the body entry is still the PC0 value 128. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def swapAmount0Out (sevm : Sevm) : B256 := Sevm.dataWord sevm 4

def swapAmount1Out (sevm : Sevm) : B256 := Sevm.dataWord sevm 36

/-- The masked recipient word the wrapper leaves on the stack. -/
def swapRecipientWord (sevm : Sevm) : B256 :=
  Sevm.dataWord sevm 68 &&& 0xffffffffffffffffffffffffffffffffffffffff

def swapRecipient (sevm : Sevm) : Adr := (Sevm.dataWord sevm 68).toAdr

/-- The head offset of the dynamic `bytes` argument, relative to the argument area. -/
def swapDataOffset (sevm : Sevm) : B256 := Sevm.dataWord sevm 100

/-- The calldata position of the first data byte (after the length word). -/
def swapDataStart (sevm : Sevm) : B256 := 32 + (4 + swapDataOffset sevm)

def swapDataLength (sevm : Sevm) : B256 := Sevm.dataWord sevm (4 + swapDataOffset sevm)

/-- The actual data bytes the wrapper passes to the body. -/
def swapData (sevm : Sevm) : Bytes :=
  sevm.data.sliceD (swapDataStart sevm).toNat (swapDataLength sevm).toNat 0

def swapDecodedEntry (sevm : Sevm) : Entry :=
  .swap (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm) (swapData sevm)

/-- The four literal wrapper guards, as modular words. -/
structure SwapAbiGuards (sevm : Sevm) : Prop where
  args : (128 : B256).toNat ≤ (sevm.data.length.toB256 - 4).toNat
  offset : (swapDataOffset sevm).toNat ≤ (0x100000000 : B256).toNat
  head : (4 + swapDataOffset sevm + 32).toNat ≤ (4 + (sevm.data.length.toB256 - 4)).toNat
  length : (swapDataLength sevm).toNat ≤ (0x100000000 : B256).toNat
  tail : (swapDataStart sevm + swapDataLength sevm).toNat ≤
    (4 + (sevm.data.length.toB256 - 4)).toNat

/-- The body's entry stack: data length, data start, recipient, amounts, return target. -/
def swapBodyStack (sevm : Sevm) : List B256 :=
  [swapDataLength sevm, swapDataStart sevm, swapRecipientWord sevm, swapAmount1Out sevm,
    swapAmount0Out sevm, 0x257, 0x022c0d9f]

/-- Literal size-check line shared by the source inverse and original cursor. -/
def swapAbiSizeLine : List Ninst := [
  .push [0x02, 0x57] (by decide), .push [4] (by decide), .reg (.dup 0),
  .reg .calldatasize, .reg .sub, .push [128] (by decide), .reg (.dup 1),
  .reg .lt, .reg .iszero, .push [0x01, 0xd4] (by decide)]

/-- The ABI size line preserves every non-gas field and computes its literal flag. -/
theorem swapAbiSizeLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b S M G) swapAbiSizeLine d) :
    ∃ G', d = St b
      (0x01d4 :: B256.eqCheck (B256.ltCheck (sevm.data.length.toB256 - 4) 128) 0 ::
        (sevm.data.length.toB256 - 4) :: 4 :: 0x0257 :: S) M G' := by
  dsimp only [swapAbiSizeLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldatasize step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_lt step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  exact ⟨gas, state⟩

/-- Literal ABI offset line, shared by both proof views. -/
def swapAbiOffsetLine : List Ninst := [
  .reg (.dup 1),
  .reg .calldataload,
  .reg (.swap 1),
  .push [0x20] (by decide),
  .reg (.dup 1),
  .reg .add,
  .reg .calldataload,
  .reg (.swap 1),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .push [0x40] (by decide),
  .reg (.dup 3),
  .reg .add,
  .reg .calldataload,
  .reg .and,
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 1),
  .reg .add,
  .reg (.swap 0),
  .push [0x80] (by decide),
  .reg (.dup 1),
  .reg .add,
  .push [0x60] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .calldataload,
  .push [0x01, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.dup 1),
  .reg .gt,
  .reg .iszero,
  .push [0x02, 0x18] (by decide)]

theorem swapAbiOffsetLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {size : B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (size :: 4 :: 0x0257 :: S) M G) swapAbiOffsetLine d) :
    ∃ G', d = St b
      ((Bytes.toB256 [0x02, 0x18]) :: (B256.eqCheck (B256.gtCheck (Sevm.dataWord sevm (4 + (Bytes.toB256 [0x60]))) (Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00])) 0) :: (Sevm.dataWord sevm (4 + (Bytes.toB256 [0x60]))) :: (4 + (Bytes.toB256 [0x80])) :: 4 :: (4 + size) :: ((Sevm.dataWord sevm (4 + (Bytes.toB256 [0x40]))) &&& (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff])) :: (Sevm.dataWord sevm (4 + (Bytes.toB256 [0x20]))) :: (Sevm.dataWord sevm 4) :: 0x0257 :: S) M G' := by
  dsimp only [swapAbiOffsetLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  dsimp only [List.set] at state
  exact ⟨gas, state⟩

/-- Literal ABI head line, shared by both proof views. -/
def swapAbiHeadLine : List Ninst := [
  .reg (.dup 2),
  .reg .add,
  .reg (.dup 3),
  .push [0x20] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .gt,
  .reg .iszero,
  .push [0x02, 0x2a] (by decide)]

theorem swapAbiHeadLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {off pad base size toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (off :: pad :: base :: size :: toWord :: a1 :: a0 :: rho :: S) M G) swapAbiHeadLine d) :
    ∃ G', d = St b
      ((Bytes.toB256 [0x02, 0x2a]) :: (B256.eqCheck (B256.gtCheck ((base + off) + (Bytes.toB256 [0x20])) size) 0) :: (base + off) :: pad :: base :: size :: toWord :: a1 :: a0 :: rho :: S) M G' := by
  dsimp only [swapAbiHeadLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  exact ⟨gas, state⟩

/-- Literal ABI tail line, shared by both proof views. -/
def swapAbiTailLine : List Ninst := [
  .reg (.dup 0),
  .reg .calldataload,
  .reg (.swap 0),
  .push [0x20] (by decide),
  .reg .add,
  .reg (.swap 1),
  .reg (.dup 4),
  .push [0x01] (by decide),
  .reg (.dup 3),
  .reg .mul,
  .reg (.dup 4),
  .reg .add,
  .reg .gt,
  .push [0x01, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg (.dup 3),
  .reg .gt,
  .reg .or,
  .reg .iszero,
  .push [0x02, 0x4c] (by decide)]

theorem swapAbiTailLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {head pad base size toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (head :: pad :: base :: size :: toWord :: a1 :: a0 :: rho :: S) M G) swapAbiTailLine d) :
    ∃ G', d = St b
      ((Bytes.toB256 [0x02, 0x4c]) :: (B256.eqCheck ((B256.gtCheck (Sevm.dataWord sevm head) (Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00])) ||| (B256.gtCheck (((Bytes.toB256 [0x20]) + head) + ((Sevm.dataWord sevm head) * (Bytes.toB256 [0x01]))) size)) 0) :: pad :: (Sevm.dataWord sevm head) :: ((Bytes.toB256 [0x20]) + head) :: base :: size :: toWord :: a1 :: a0 :: rho :: S) M G' := by
  dsimp only [swapAbiTailLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mul step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_or step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  dsimp only [List.set] at state
  exact ⟨gas, state⟩

/-- Literal ABI call line, shared by both proof views. -/
def swapAbiCallLine : List Ninst := [
  .reg .pop,
  .reg (.swap 0),
  .reg (.swap 2),
  .reg .pop,
  .reg (.swap 0),
  .reg .pop,
  .push [0x06, 0x83] (by decide)]

theorem swapAbiCallLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {pad len start base size toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (pad :: len :: start :: base :: size :: toWord :: a1 :: a0 :: rho :: S) M G) swapAbiCallLine d) :
    ∃ G', d = St b
      ((Bytes.toB256 [0x06, 0x83]) :: len :: start :: toWord :: a1 :: a0 :: rho :: S) M G' := by
  dsimp only [swapAbiCallLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  dsimp only [List.set] at state
  exact ⟨gas, state⟩

/-- Actual PC0, selector dispatch and ABI wrapper: a successful swap run derives the
nonpayable/size guards, the four literal wrapper guards, and the body's same-D internal call
with its decoded entry stack and the PC0 memory, followed by the original stop tail. -/
theorem swapPc0_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : SFunc.RunP (StepIn D) cert.prog sevm (St b [] Mem.empty G) t_0000_c0 o) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧ SwapAbiGuards sevm ∧
      ∃ calleeGas calleePost,
        SFunc.RunP (StepIn D) cert.prog sevm
          (St b (swapBodyStack sevm) getterInitMemory calleeGas) t_0683_c54 (.returned calleePost) ∧
        SFunc.RunCutP (StepIn D) cert.prog sevm [] calleePost t_0257_c99 (.done o) := by
  obtain ⟨value, size, G0, guarded⟩ := syncGuards_inv run
  have run := SFunc.runP_iff_runCutP_nil.mp guarded
  refine ⟨value, size, ?_⟩
  unfold t_001a_c0 at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_calldataload (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_shr (StepIn.toRun hs)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0x022c0d9f : B256) from selector] at eq
  subst d
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a,0x62,0x78,0x42]) (0x022c0d9f : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_00f9_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x23,0xb8,0x72,0xdd]) (0x022c0d9f : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_0166_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_gtP (fun h => StepIn.toRun h) run
  simp only [show B256.gtCheck (Bytes.toB256 [0x09,0x5e,0xa7,0xb3]) (0x022c0d9f : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_0197_c0 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, run⟩ := ric_cmp_eqP (fun h => StepIn.toRun h)
    (g := t_01be_c99) (by intro bad; cases bad) rfl run
  simp only [show B256.eqCheck (Bytes.toB256 [0x02,0x2c,0x0d,0x9f]) (0x022c0d9f : B256) = 1
    from by decide, show ¬ ((1 : B256) = 0) from by decide, ite_false] at run
  unfold t_01be_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapAbiSizeLine run
  obtain ⟨_, rfl⟩ := swapAbiSizeLine_inv line
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨g1, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_01d0_c99.noOk = true))
  unfold t_01d4_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapAbiOffsetLine run
  obtain ⟨_, rfl⟩ := swapAbiOffsetLine_inv line
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨g2, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_0214_c99.noOk = true))
  unfold t_0218_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapAbiHeadLine run
  obtain ⟨_, rfl⟩ := swapAbiHeadLine_inv line
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨g3, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_0226_c99.noOk = true))
  unfold t_022a_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapAbiTailLine run
  obtain ⟨_, rfl⟩ := swapAbiTailLine_inv line
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨g4, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_0248_c99.noOk = true))
  unfold t_024c_c99 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapAbiCallLine run
  obtain ⟨_, rfl⟩ := swapAbiCallLine_inv line
  have e32 : Bytes.toB256 [32] = (32 : B256) := rfl
  have e100 : (4 : B256) + Bytes.toB256 [96] = 100 := by decide
  have e36 : (4 : B256) + 32 = 36 := by decide
  have e68 : (4 : B256) + Bytes.toB256 [64] = 68 := by decide
  simp only [e32, e100, e36, e68,
    show Bytes.toB256 [1, 0, 0, 0, 0] = (0x100000000 : B256) from rfl,
    show Bytes.toB256 [1] = (1 : B256) from rfl] at g1 g2 g3 g4 run
  have mulOne : ∀ x : B256, x * 1 = x := by
    intro x
    apply B256.toNat_inj
    rw [B256.toNat_mul, show (1 : B256).toNat = 1 from rfl, Nat.mul_one,
      Nat.lo_eq_of_lt x.toNat_lt]
  simp only [mulOne] at g4
  have bit : ∀ a b : B256, B256.gtCheck a b = 0 ∨ B256.gtCheck a b = 1 := by
    intro a b
    unfold B256.gtCheck
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have orZero : ∀ a b c e : B256, (B256.gtCheck a b ||| B256.gtCheck c e) = 0 →
      B256.gtCheck a b = 0 ∧ B256.gtCheck c e = 0 := by
    intro a b c e h
    rcases bit a b with p | p <;> rcases bit c e with q | q <;> rw [p, q] at h ⊢ <;>
      first
        | exact ⟨rfl, rfl⟩
        | exact absurd h (by decide)
  have split4 := orZero _ _ _ _ (eq_zero_of_iszero_ne_zero g4)
  refine ⟨⟨toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero g1),
    toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero g2),
    toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero g3),
    toNat_le_of_gtCheck_eq_zero split4.1, toNat_le_of_gtCheck_eq_zero split4.2⟩, ?_⟩
  cases run with
  | callHalt d lookup pop callee =>
      change some t_0683_c54 = _ at lookup
      cases lookup
      exact False.elim (callee.not_halted_entry
        (S := [2, 3, 4, 5, 6, 7, 8, 9, 16, 17, 18, 19, 20, 21, 22, 54, 56, 57, 58, 59, 60, 65, 66, 71])
        (by decide +kernel) (by decide : 54 ∈ [2, 3, 4, 5, 6, 7, 8, 9, 16, 17, 18, 19, 20, 21, 22, 54, 56, 57,
          58, 59, 60, 65, 66, 71])
        (by rfl : cert.prog[54]? = some t_0683_c54) rfl)
  | callRet d lookup pop callee body =>
      change some t_0683_c54 = _ at lookup
      cases lookup
      exact ⟨_, _, (St.of_pop1 pop).2 ▸ callee, body⟩

end Blanc.Lift.UniswapV2Pair
