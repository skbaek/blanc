import Blanc.Lift.UniswapV2Pair.SkimSecondWalk

/-! Actual Burn post-transfer balance observations at the moved free pointer. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive BurnFinalBalanceSite where
  | first
  | second

def BurnFinalBalanceSite.callTree : BurnFinalBalanceSite → SFunc
  | .first => t_170f_c13
  | .second => t_17ab_c13

def BurnFinalBalanceSite.returnTree : BurnFinalBalanceSite → SFunc
  | .first => t_1723_c13
  | .second => t_17bf_c13

def BurnFinalBalanceSite.decodeTree : BurnFinalBalanceSite → SFunc
  | .first => t_1739_c13
  | .second => t_17d5_c13

def BurnFinalBalanceSite.afterDecodeTree (site : BurnFinalBalanceSite) : SFunc :=
  match site.decodeTree with
  | .dest (.next _ (.next _ tail)) => tail
  | _ => .undefined

def burnBalanceReplyMemory (M : Mem) (p : B256) (out : Bytes) : Mem :=
  (M.extends [(p.toNat, 36), (p.toNat, 32)]).write p.toNat (out.take 32)

theorem burnBalanceReplyMemory_extended {M : Mem} {p : B256} {n : Nat}
    (mem : PtrMem p n M) (fit : p.toNat + 36 ≤ n) :
    M.extends [(p.toNat, 36), (p.toNat, 32)] = M := by
  unfold Mem.extends
  rw [mem.size]
  simp only [memExtsSize]
  rw [memExtSize_of_le mem.n32 fit,
    memExtSize_of_le mem.n32 (by omega : p.toNat + 32 ≤ n), ← mem.size]

theorem burnBalanceReplyMemory_ptr {M : Mem} {p : B256} {n : Nat} (out : Bytes)
    (mem : PtrMem p n M) (low : 96 ≤ p.toNat) (fit : p.toNat + 36 ≤ n) :
    PtrMem p n (burnBalanceReplyMemory M p out) := by
  unfold burnBalanceReplyMemory
  rw [burnBalanceReplyMemory_extended mem fit]
  exact mem.write_bytes_of_le p.toNat (out.take 32)
    (by have := List.length_take_le 32 out; omega) (Or.inr low)

theorem burnBalanceReplyMemory_word {M : Mem} {p : B256} {n : Nat} {out : Bytes}
    (mem : PtrMem p n M) (fit : p.toNat + 36 ≤ n) (long : 32 ≤ out.length) :
    Bytes.toB256 ((burnBalanceReplyMemory M p out).read p.toNat 32).1 =
      Bytes.toB256 (out.take 32) := by
  have length : (out.take 32).length = 32 := by rw [List.length_take, Nat.min_eq_left long]
  have image := Bytes.sliceD_writeAt M.data.toList (out.take 32) p.toNat
  rw [length] at image
  unfold burnBalanceReplyMemory
  rw [burnBalanceReplyMemory_extended mem fit,
    (Mem.reads_data M |>.write mem.wf p.toNat (out.take 32)).read, image]

def burnFinalFirstRequestLine : List Ninst := [
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [4] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 9),
  .reg .and,
  .reg (.swap 1),
  .push [0x70, 0xa0, 0x82, 0x31] (by decide),
  .reg (.swap 1),
  .push [0x24] (by decide),
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .add,
  .reg (.swap 2),
  .push [0x20] (by decide),
  .reg (.swap 2),
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 2),
  .reg (.swap 0),
  .reg .sub,
  .reg .add,
  .reg (.dup 1),
  .reg (.dup 6),
  .reg (.dup 0)]

theorem burnFinalFirstRequestLine_inv {sevm : Sevm} {b final : Devm}
    {R : List B256} {M : Mem} {G : Nat} {p : B256}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (ptr : PtrWord p M) (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : Line.Run sevm
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      burnFinalFirstRequestLine final) :
    ∃ gas, final = St b
      ((token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      (skimRequestMemory M p sevm.currentTarget) gas := by
  have word0 := ptr.2
  have p4 : (p + Bytes.toB256 [4]).toNat = p.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by change p.toNat + 4 < 2 ^ 256; omega)
  have word1 : Bytes.toB256 ((((M.read 64 32).2.write p.toNat balanceOfSelectorWord.toBytes).write
      (p + Bytes.toB256 [4]).toNat sevm.currentTarget.toB256.toBytes).read 64 32).1 = p :=
    (((ptr.extend 64 32).write p.toNat _ low).write (p + Bytes.toB256 [4]).toNat _
      (by rw [p4]; omega)).2
  dsimp only [balanceOfSelectorWord] at word1
  dsimp only [burnFinalFirstRequestLine, burnPricedLocals] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word0] at state
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  have address := of_run_address hs
  have stack := address.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have state := St.of_stackRel address
  rw [stack] at state
  rw [state] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word1] at state
  subst d
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

/-- The two physical reply bounds leave room for the complete following
balance-query staging area, beyond the final64-byte ABI area. -/
theorem burnFinalPointer_bounds {firstReply secondReply : Bytes}
    (firstWidth : firstReply.length < 2 ^ 160)
    (secondWidth : secondReply.length < 2 ^ 160) :
    96 ≤ (burnSecondTransferPointer firstReply secondReply).toNat ∧
      (burnSecondTransferPointer firstReply secondReply).toNat + 1024 < 2 ^ 256 := by
  have first := burnFirstTransferPointer_layout firstWidth
  have second := burnSecondTransferPointer_layout firstWidth secondWidth
  have firstDivision := Nat.mod_add_div (firstReply.length + 63) 32
  have secondDivision := Nat.mod_add_div (secondReply.length + 63) 32
  have firstBound : (burnFirstTransferPointer firstReply).toNat ≤ firstReply.length + 355 := by
    rw [first.1]
    split <;> omega
  have secondBound : (burnSecondTransferPointer firstReply secondReply).toNat ≤
      firstReply.length + secondReply.length + 582 := by
    rw [second.1]
    split <;> omega
  have margin : 2 * 2 ^ 160 + 1606 < (2 ^ 256 : Nat) := by decide
  exact ⟨by have := second.2.1; have := first.2.1; omega, by omega⟩

/-- Literal overlapping request writes preserve the moved pointer and pay
for the entire36-byte calldata/output window. -/
theorem burnBalanceRequest_memoryLayout {M : Mem} {p : B256} {n : Nat} {pair : Adr}
    (mem : PtrMem p n M) (low : 96 ≤ p.toNat)
    (high : p.toNat + 1024 < 2 ^ 256) :
    PtrMem p (skimRequestMemory M p pair).size (skimRequestMemory M p pair) ∧
      p.toNat + 36 ≤ (skimRequestMemory M p pair).size := by
  have p4 : (p + 4).toNat = p.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by change p.toNat + 4 < 2 ^ 256; omega)
  have first := (mem.extend 64 32).write p.toNat balanceOfSelectorWord (Or.inr low)
  have second := first.write (p + 4).toNat pair.toB256 (Or.inr (by rw [p4]; omega))
  have image := second.extend 64 32
  have covered := Jaune.memExtSize_access_le
    (memExtSize (memExtSize n 64 32) p.toNat 32) (p + 4).toNat 32 (by decide)
  have grown := Blanc.Lift.memExtSize_ge
    (memExtSize (memExtSize (memExtSize n 64 32) p.toNat 32) (p + 4).toNat 32) 64 32
  have fit : p.toNat + 36 ≤ (skimRequestMemory M p pair).size := by
    rw [p4] at covered grown
    have size : (skimRequestMemory M p pair).size =
        memExtSize (memExtSize (memExtSize (memExtSize n 64 32) p.toNat 32)
          (p + 4).toNat 32) 64 32 := image.size
    rw [size, p4]
    omega
  have sized : PtrMem p (skimRequestMemory M p pair).size (skimRequestMemory M p pair) := by
    have size : (skimRequestMemory M p pair).size =
        memExtSize (memExtSize (memExtSize (memExtSize n 64 32) p.toNat 32)
          (p + 4).toNat 32) 64 32 := image.size
    rw [size]
    exact image
  exact ⟨sized, fit⟩

def burnFinalSecondRequestLine : List Ninst := [
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .push [0x70, 0xa0, 0x82, 0x31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .reg .address,
  .push [4] (by decide),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.swap 0),
  .reg .mload,
  .reg (.swap 1),
  .reg (.swap 6),
  .reg .pop,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 8),
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

theorem burnFinalSecondRequestLine_inv {sevm : Sevm} {b final : Devm}
    {R : List B256} {M : Mem} {G : Nat} {p : B256}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ balance0 : B256}
    (ptr : PtrWord p M) (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : Line.Run sevm
      (St b (balance0 :: burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      burnFinalSecondRequestLine final) :
    ∃ gas, final = St b
      ((token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: p :: 36 :: p :: 32 ::
        (p + 36) :: 0x70a08231 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        burnPricedLocals supply f L b1 balance0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
      (skimRequestMemory M p sevm.currentTarget) gas := by
  have word0 := ptr.2
  have p4 : (p + Bytes.toB256 [4]).toNat = p.toNat + 4 :=
    B256.toNat_add_eq_of_nof _ _ (by change p.toNat + 4 < 2 ^ 256; omega)
  have word1 : Bytes.toB256 ((((M.read 64 32).2.write p.toNat balanceOfSelectorWord.toBytes).write
      (p + Bytes.toB256 [4]).toNat sevm.currentTarget.toB256.toBytes).read 64 32).1 = p :=
    (((ptr.extend 64 32).write p.toNat _ low).write (p + Bytes.toB256 [4]).toNat _
      (by rw [p4]; omega)).2
  dsimp only [balanceOfSelectorWord] at word1
  dsimp only [burnFinalSecondRequestLine, burnPricedLocals] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word0] at state
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run
  have address := of_run_address hs
  have stack := address.stack
  simp only [Stack.Push, Split, St.stack] at stack
  have state := St.of_stackRel address
  rw [stack] at state
  rw [state] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl, word1] at state
  subst d
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
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

end Blanc.Lift.UniswapV2Pair
