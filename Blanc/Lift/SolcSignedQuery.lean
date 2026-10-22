import Blanc.AddressSlotProofs
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorQuietReturn
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.InvWalkStep
import Blanc.Lift.MapSlot
import Blanc.Lift.RunPWalk
import Blanc.Lift.WordImage

/-! Shared inversions for Solidity signed-query source fragments.
Concrete code, checked certificates and actual cursor routes remain with consumers. -/

namespace Blanc.Lift.SolcSignedQuery

open Jaune Blanc Blanc.Lift

/-- Hash of the actual six ABI words, with the first word supplied by source. -/
def sixWordHash (tag : B256) (owner spender : Adr) (value nonce deadline : B256) : B256 :=
  (tag.toBytes ++ owner.toB256.toBytes ++ spender.toB256.toBytes ++
    value.toBytes ++ nonce.toBytes ++ deadline.toBytes).keccak

/-- The compiler shuffle after the signed-query helper returns. -/
def recoveryEpilogue : SFunc :=
  .dest (([.reg (.swap 7), .reg (.swap 6), .reg .pop, .reg .pop, .reg .pop,
    .reg .pop, .reg .pop, .reg .pop, .reg .pop] : List Ninst).foldr SFunc.next .ret)

theorem recovery_epilogue
    {fs : List SFunc} {sevm : Sevm} {b D : Devm} {M : Mem} {G : Nat}
    {answer digest s r v domain ret owner : B256} {S : List B256}
    (run : SFunc.Run fs sevm
      (St b (answer :: digest :: 0 :: 128 :: s :: r :: v :: domain :: ret :: owner :: S) M G)
      recoveryEpilogue (.returned D)) :
    ∃ G', D = St b (answer :: owner :: S) M G' := by
  unfold recoveryEpilogue at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := rpw_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  exact rpw_ret run

def prologue (d0 d1 : UInt8) : List Ninst :=
  [.push [0x80] (by decide), .push [0x40] (by decide), .reg .mstore,
   .reg .callvalue, .reg (.dup 0), .reg .iszero, .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem prologue_line {d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem}
    {G : Nat} {S : List B256}
    (run : Line.Run sevm (St b S M G) (prologue d0 d1) d) :
    ∃ G', d = St b ((Bytes.toB256 [d0, d1]) :: B256.eqCheck sevm.value 0 :: sevm.value :: S)
      (M.write 64 (128 : B256).toBytes) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_callvalue step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

def sizeLine (d0 d1 : UInt8) : List Ninst :=
  [.reg .pop, .push [0x04] (by decide), .reg .calldatasize, .reg .lt,
   .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem size_line {d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem}
    {G : Nat} {value : B256}
    (run : Line.Run sevm (St b [value] M G) (sizeLine d0 d1) d) :
    ∃ G', d = St b [(Bytes.toB256 [d0, d1]), B256.ltCheck sevm.data.length.toB256 4] M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldatasize step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_lt step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

def decodeLine (d0 d1 : UInt8) : List Ninst :=
  [.reg .pop,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup 1),
   .reg .calldataload,
   .reg (.dup 1),
   .reg .and,
   .reg (.swap 1),
   .push [0x20] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .and,
   .reg (.swap 0),
   .push [0x40] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0x60] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0xff] (by decide),
   .push [0x80] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg .calldataload,
   .reg .and,
   .reg (.swap 0),
   .push [0xa0] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0xc0] (by decide),
   .reg .add,
   .reg .calldataload,
   .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem decode_line {d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {available : B256} {S : List B256}
    (run : Line.Run sevm (St b (available :: 4 :: S) M G) (decodeLine d0 d1) d) :
    ∃ G', d = St b
      ((Bytes.toB256 [d0, d1]) :: Sevm.dataWord sevm 196 :: Sevm.dataWord sevm 164 ::
        (Sevm.dataWord sevm 132 &&& 255) :: Sevm.dataWord sevm 100 :: Sevm.dataWord sevm 68 ::
        (Sevm.dataWord sevm 36).toAdr.toB256 :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
        S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  simp only [ff20_and_word]
  exact ⟨_, rfl⟩

def pauseLine (slot d0 d1 : UInt8) : List Ninst :=
  [.push [slot] (by simp only [List.length_cons, List.length_nil]; decide), .reg .sload,
   .push [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
   .reg (.swap 0), .reg .div, .push [0xff] (by decide), .reg .and,
   .reg .iszero, .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem pause_line {slot d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {S : List B256} (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b S M G) (pauseLine slot d0 d1) d) :
    ∃ G', d = St (afterSload sevm b (Bytes.toB256 [slot]))
      ((Bytes.toB256 [d0, d1]) :: B256.eqCheck (255 &&& (b.getStorVal sevm.currentTarget (Bytes.toB256 [slot]) /
        (0x10000000000000000000000000000000000000000 : B256))) 0 :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_div step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

def mappedByteReadLine (depth : Fin 15) (base : UInt8) : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup ⟨depth.val + 1, by omega⟩),
   .reg .and,
   .push [0x00] (by decide),
   .reg (.swap 0),
   .reg (.dup 1),
   .reg .mstore,
   .push [base] (by simp only [List.length_cons, List.length_nil]; decide),
   .push [0x20] (by decide),
   .reg .mstore,
   .push [0x40] (by decide),
   .reg (.swap 0),
   .reg .keccak256,
   .reg .sload,
   .reg (.dup ⟨depth.val + 1, by omega⟩),
   .reg (.swap 0),
   .push [0xff] (by decide),
   .reg .and,
   .reg .iszero]

theorem mapped_byte_read_line {depth : Fin 15} {base : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {owner : Adr} {S : List B256}
    (source : S[depth.val]? = some owner.toB256)
    (ptr : PtrMem 128 96 M) (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm
      (St b S M G)
      (mappedByteReadLine depth base) d) :
    ∃ G', d = St (afterSload sevm b (mapSlot owner.toB256 (Bytes.toB256 [base])))
      (B256.eqCheck (255 &&& b.getStorVal sevm.currentTarget (mapSlot owner.toB256 (Bytes.toB256 [base]))) 0 ::
        owner.toB256 :: S)
      ((M.write 0 owner.toB256.toBytes).write 32 (Bytes.toB256 [base]).toBytes) G' := by
  have ptr' := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 (Bytes.toB256 [base]) (.inl (by decide))
  change PtrMem 128 96 ((M.write 0 owner.toB256.toBytes).write 32 (Bytes.toB256 [base]).toBytes) at ptr'
  have noGrowth := ptr'.read_self (i := 0) (sz := 64) (by decide)
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup (by simpa only [List.getElem?_cons_succ] using source) step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_and step
  rw [B256.and_comm, ff20_and_word, toAdr_toB256] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_keccak step
  rw [keccak_scratch] at state
  rw [show (Bytes.toB256 [0x00]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    show (Bytes.toB256 [0x20]).toNat = 32 from rfl,
    noGrowth] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup (by simpa only [List.getElem?_cons_succ] using source) step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  cases run
  exact ⟨_, rfl⟩

def blacklistReadLine (base : UInt8) : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup 7),
   .reg .and,
   .push [0x00] (by decide),
   .reg (.swap 0),
   .reg (.dup 1),
   .reg .mstore,
   .push [base] (by simp only [List.length_cons, List.length_nil]; decide),
   .push [0x20] (by decide),
   .reg .mstore,
   .push [0x40] (by decide),
   .reg (.swap 0),
   .reg .keccak256,
   .reg .sload,
   .reg (.dup 7),
   .reg (.swap 0),
   .push [0xff] (by decide),
   .reg .and,
   .reg .iszero]

theorem blacklist_read_line {base : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {a0 a1 a2 a3 a4 a5 : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 128 96 M) (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm
      (St b (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S) M G)
      (blacklistReadLine base) d) :
    ∃ G', d = St (afterSload sevm b (mapSlot owner.toB256 (Bytes.toB256 [base])))
      (B256.eqCheck (255 &&& b.getStorVal sevm.currentTarget (mapSlot owner.toB256 (Bytes.toB256 [base]))) 0 ::
        owner.toB256 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: owner.toB256 :: S)
      ((M.write 0 owner.toB256.toBytes).write 32 (Bytes.toB256 [base]).toBytes) G' := by
  exact mapped_byte_read_line (depth := ⟨6, by decide⟩) rfl ptr fork run


def nonceLine (base : UInt8) : List Ninst :=
  [.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup 0),
   .reg (.dup 8),
   .reg .and,
   .push [0x00] (by decide),
   .reg (.dup 1),
   .reg (.dup 1),
   .reg .mstore,
   .push [base] (by simp only [List.length_cons, List.length_nil]; decide),
   .push [0x20] (by decide),
   .reg (.swap 0),
   .reg (.dup 1),
   .reg .mstore,
   .push [0x40] (by decide),
   .reg (.swap 1),
   .reg (.dup 2),
   .reg (.swap 0),
   .reg .keccak256,
   .reg (.dup 0),
   .reg .sload,
   .push [0x01] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .sstore]

theorem nonce_line {base : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v deadline value : B256} {spender owner : Adr} {S : List B256}
    (ptr : PtrMem 128 96 M) (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b
      (s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M G)
      (nonceLine base) d) :
    let nonce := b.getStorVal sevm.currentTarget (mapSlot owner.toB256 (Bytes.toB256 [base]))
    ∃ G', d = St (afterSstore sevm (afterSload sevm b (mapSlot owner.toB256 (Bytes.toB256 [base])))
      (mapSlot owner.toB256 (Bytes.toB256 [base])) (nonce + 1))
      (nonce :: 32 :: 64 :: owner.toB256 ::
        (0xffffffffffffffffffffffffffffffffffffffff : B256) ::
        s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      ((M.write 0 owner.toB256.toBytes).write 32 (Bytes.toB256 [base]).toBytes) G' := by
  have ptr' := (ptr.write 0 owner.toB256 (.inl (by decide))).write 32 (Bytes.toB256 [base]) (.inl (by decide))
  change PtrMem 128 96 ((M.write 0 owner.toB256.toBytes).write 32 (Bytes.toB256 [base]).toBytes) at ptr'
  have noGrowth := ptr'.read_self (i := 0) (sz := 64) (by decide)
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_and step
  rw [B256.and_comm, ff20_and_word, toAdr_toB256] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_keccak step
  rw [keccak_scratch] at state
  rw [show (Bytes.toB256 [0x00]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    show (Bytes.toB256 [0x20]).toNat = 32 from rfl,
    noGrowth] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sstore fork step
  cases run
  exact ⟨_, rfl⟩

def structHeadMemory (tag : B256) (M : Mem) (owner : Adr) : Mem :=
  (M.write 160 (tag : B256).toBytes).write
    192 owner.toB256.toBytes

def structBodyMemory (M : Mem) (spender : Adr) (value nonce deadline : B256) : Mem :=
  (((M.write 224 spender.toB256.toBytes).write 256 value.toBytes).write
    288 nonce.toBytes).write 320 deadline.toBytes

def structMemory (tag : B256) (M : Mem) (owner spender : Adr) (value nonce deadline : B256) : Mem :=
  let M := structHeadMemory tag M owner
  let M := structBodyMemory M spender value nonce deadline
  (M.write 128 (192 : B256).toBytes).write 64 (352 : B256).toBytes

def bufferHeadLine (tag : Bytes) (le : tag.length ≤ 32) : List Ninst :=
  [.reg (.dup 2),
   .reg .mload,
   .push tag le,
   .reg (.swap 2),
   .reg (.dup 1),
   .reg .add,
   .reg (.swap 2),
   .reg (.swap 0),
   .reg (.swap 2),
   .reg .mstore,
   .reg (.dup 1),
   .reg (.dup 3),
   .reg .add,
   .reg (.dup 4),
   .reg (.swap 0),
   .reg .mstore,
   .reg (.swap 3)]

theorem buffer_head_line {tag : Bytes} {le : tag.length ≤ 32} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {nonce s r v deadline value : B256} {spender owner : Adr} {S : List B256}
    (ptr : PtrMem 128 96 M)
    (run : Line.Run sevm (St b
      (nonce :: 32 :: 64 :: owner.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff : B256) ::
       s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M G)
      (bufferHeadLine tag le) d) :
    ∃ G', d = St b
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) :: 128 :: 64 :: owner.toB256 :: nonce ::
       s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      (structHeadMemory (Bytes.toB256 tag) M owner) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  simp only at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  cases run
  exact ⟨_, rfl⟩

def bufferBodyLine : List Ninst :=
  [.reg (.dup 10),
   .reg .and,
   .push [0x60] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg .mstore,
   .push [0x80] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg (.dup 9),
   .reg (.swap 0),
   .reg .mstore,
   .push [0xa0] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg (.swap 3),
   .reg (.swap 0),
   .reg (.swap 3),
   .reg .mstore,
   .push [0xc0] (by decide),
   .reg (.dup 0),
   .reg (.dup 4),
   .reg .add,
   .reg (.dup 8),
   .reg (.swap 0),
   .reg .mstore]

theorem buffer_body_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {nonce s r v deadline value : B256} {spender owner : Adr} {S : List B256}
    (run : Line.Run sevm (St b
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) :: 128 :: 64 :: owner.toB256 :: nonce ::
       s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S) M G)
      bufferBodyLine d) :
    ∃ G', d = St b
      (192 :: 64 :: owner.toB256 :: 128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      (structBodyMemory M spender value nonce deadline) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_and step
  have canonical : (spender.toB256 &&& (0xffffffffffffffffffffffffffffffffffffffff : B256)) = spender.toB256 := by
    change (spender.toB256 &&& Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) = _
    rw [B256.and_comm, ff20_and_word, toAdr_toB256]
  rw [canonical] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  simp only at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  cases run
  exact ⟨_, rfl⟩

def bufferTailLine (slot r0 r1 d0 d1 : UInt8) : List Ninst :=
  [.reg (.dup 1),
   .reg .mload,
   .reg (.dup 0),
   .reg (.dup 5),
   .reg .sub,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .add,
   .reg (.dup 1),
   .reg .mstore,
   .push [0xe0] (by decide),
   .reg (.swap 0),
   .reg (.swap 3),
   .reg .add,
   .reg (.swap 0),
   .reg .mstore,
   .push [slot] (by simp only [List.length_cons, List.length_nil]; decide),
   .reg .sload,
   .push [r0, r1] (by simp only [List.length_cons, List.length_nil]; decide),
   .reg (.swap 0),
   .reg (.dup 6),
   .reg (.dup 6),
   .reg (.dup 6),
   .reg (.dup 6),
   .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem buffer_tail_line {slot r0 r1 d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v deadline value : B256} {spender owner : Adr} {S : List B256}
    (ptr : PtrMem 128 352 M) (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b
      (192 :: 64 :: owner.toB256 :: 128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      M G) (bufferTailLine slot r0 r1 d0 d1) d) :
    ∃ G', d = St (afterSload sevm b (Bytes.toB256 [slot]))
      ((Bytes.toB256 [d0, d1]) :: 128 :: s :: r :: v :: b.getStorVal sevm.currentTarget (Bytes.toB256 [slot]) :: (Bytes.toB256 [r0, r1]) ::
       owner.toB256 :: 128 :: s :: r :: v :: deadline :: value :: spender.toB256 :: owner.toB256 :: S)
      ((M.write 128 (192 : B256).toBytes).write 64 (352 : B256).toBytes) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word, ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  simp only [List.set_cons_zero] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  simp only at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

theorem struct_memory_facts {tag : B256} {M : Mem} {owner spender : Adr}
    {value nonce deadline : B256} (ptr : PtrMem 128 96 M) :
    PtrMem 352 352 (structMemory tag M owner spender value nonce deadline) ∧
    memWord (structMemory tag M owner spender value nonce deadline) 128 = 192 ∧
    ((structMemory tag M owner spender value nonce deadline).read 160 192).1.keccak =
      sixWordHash tag owner spender value nonce deadline := by
  have p1 := (ptr.write 160
    (tag : B256)
    (.inr (by decide))).write 192 owner.toB256 (.inr (by decide))
  have p2 := (((p1.write 224 spender.toB256 (.inr (by decide))).write 256 value
    (.inr (by decide))).write 288 nonce (.inr (by decide))).write 320 deadline (.inr (by decide))
  have p3 := (p2.write 128 192 (.inr (by decide))).set (q := 352)
  refine ⟨p3, ?_, ?_⟩
  · unfold structMemory
    rw [memWord_congr (μ := (structBodyMemory (structHeadMemory tag M owner) spender value nonce deadline).write 128 (192 : B256).toBytes)
      (fun j hj => ?_)]
    · exact (Mem.memWord_write_word _ 128 192).1
    · exact (Mem.write_agree _ 64 (352 : B256).toBytes).2 (128 + j)
        (by
          have hs : ((structBodyMemory (structHeadMemory tag M owner) spender value nonce deadline).write
            128 (192 : B256).toBytes).size = 352 := (p2.write 128 192 (.inr (by decide))).size
          rw [hs]
          omega)
        (by rw [B256.length_toBytes]; omega)
  · have image := (Mem.reads_data M).write ptr.wf 160
      (tag : B256).toBytes
    have wf := ptr.wf.write 160
      (tag : B256).toBytes
    have image := image.write wf 192 owner.toB256.toBytes
    have wf := wf.write 192 owner.toB256.toBytes
    have image := image.write wf 224 spender.toB256.toBytes
    have wf := wf.write 224 spender.toB256.toBytes
    have image := image.write wf 256 value.toBytes
    have wf := wf.write 256 value.toBytes
    have image := image.write wf 288 nonce.toBytes
    have wf := wf.write 288 nonce.toBytes
    have image := image.write wf 320 deadline.toBytes
    have wf := wf.write 320 deadline.toBytes
    have image := image.write wf 128 (192 : B256).toBytes
    have wf := wf.write 128 (192 : B256).toBytes
    have image := image.write wf 64 (352 : B256).toBytes
    unfold structMemory structBodyMemory structHeadMemory
    rw [Mem.Reads.read image,
      Bytes.sliceD_writeAt_word_after _ 64 160 192 352 (by decide),
      Bytes.sliceD_writeAt_word_after _ 128 160 192 192 (by decide),
      Bytes.sliceD_writeAt_word_last _ 160 160 320 192 deadline rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 128 288 160 nonce rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 96 256 128 value rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 64 224 96 spender.toB256 rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 32 192 64 owner.toB256 rfl rfl,
      sliceD_word_same]
    rfl

/-- Typed-data image at the actual allocated struct-buffer end. -/
def typedWordsAt (p : B256) (M : Mem) (domain structHash : B256) : Mem :=
  ((M.write (32 + p).toNat
    (0x1901000000000000000000000000000000000000000000000000000000000000 : B256).toBytes).write
    (34 + p).toNat domain.toBytes).write (66 + p).toNat structHash.toBytes

def typedMemoryAt (p : B256) (M : Mem) (domain structHash : B256) : Mem :=
  ((typedWordsAt p M domain structHash).write p.toNat (66 : B256).toBytes).write
    64 (98 + p).toBytes

def typedWords (M : Mem) (domain structHash : B256) : Mem :=
  typedWordsAt 352 M domain structHash

def typedMemory (M : Mem) (domain structHash : B256) : Mem :=
  typedMemoryAt 352 M domain structHash

def structHashLine : List Ninst :=
  [.reg (.dup 0),
   .reg .mload,
   .push [0x20] (by decide),
   .reg (.dup 0),
   .reg (.dup 3),
   .reg .add,
   .reg (.swap 1),
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .keccak256]

theorem struct_hash_line_at {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {ret s r v domain hash len p : B256} {n : Nat} {owner : Adr} {S : List B256}
    (ptr : PtrMem p n M) (length : memWord M 128 = len)
    (fit : 160 + len.toNat ≤ n)
    (hashRead : (M.read 160 len.toNat).1.keccak = hash)
    (run : Line.Run sevm (St b
      (128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G)
      structHashLine d) :
    ∃ G', d = St b
      (hash :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 128 :: _) (Mem.read M 128 32).2 _ at state
  rw [length, ptr.read_self (by omega)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_keccak step
  change _ = St _ ((M.read 160 len.toNat).1.keccak :: _) (Mem.read M 160 len.toNat).2 _ at state
  rw [hashRead, ptr.read_self fit] at state
  subst state
  cases run
  exact ⟨_, rfl⟩

theorem struct_hash_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {ret s r v domain hash : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 352 352 M) (length : memWord M 128 = 192)
    (hashRead : (M.read 160 192).1.keccak = hash)
    (run : Line.Run sevm (St b
      (128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G)
      structHashLine d) :
    ∃ G', d = St b
      (hash :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G' := by
  exact struct_hash_line_at ptr length (by decide) hashRead run

def typedWordsLine : List Ninst :=
  [.push [0x40] (by decide),
   .reg (.dup 0),
   .reg .mload,
   .push [0x19, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
   .reg (.dup 1),
   .reg (.dup 5),
   .reg .add,
   .reg .mstore,
   .push [0x22] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg (.dup 9),
   .reg (.swap 0),
   .reg .mstore,
   .push [0x42] (by decide),
   .reg (.dup 0),
   .reg (.dup 2),
   .reg .add,
   .reg (.swap 3),
   .reg (.swap 0),
   .reg (.swap 3),
   .reg .mstore]

theorem typed_words_line_at {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {ret s r v domain hash p : B256} {n : Nat} {owner : Adr} {S : List B256}
    (layout : p = 352 ∨ p = 384) (ptr : PtrMem p n M)
    (run : Line.Run sevm (St b
      (hash :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G)
      typedWordsLine d) :
    ∃ G', d = St b
      (p :: 64 :: 66 :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S)
      (typedWordsAt p M domain hash) G' := by
  rcases layout with rfl | rfl <;>
  (
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, state⟩ := ri_mload step
    change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
    rw [ptr.word, ptr.read_self ptr.ge] at state
    subst state
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_add step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_mstore step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_add step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_mstore step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_add step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_swap rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_mstore step
    cases run
    exact ⟨_, rfl⟩
  )

theorem typed_words_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {ret s r v domain hash : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 352 352 M)
    (run : Line.Run sevm (St b
      (hash :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G)
      typedWordsLine d) :
    ∃ G', d = St b
      (352 :: 64 :: 66 :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S)
      (typedWords M domain hash) G' := by
  exact typed_words_line_at (Or.inl rfl) ptr run

def typedLengthLine : List Ninst :=
  [.reg (.dup 1),
   .reg .mload,
   .reg (.dup 0),
   .reg (.dup 2),
   .reg .sub,
   .reg (.swap 0),
   .reg (.swap 3),
   .reg .add,
   .reg (.dup 3),
   .reg .mstore,
   .push [0x62] (by decide),
   .reg .add,
   .reg (.swap 0),
   .reg .mstore]

theorem typed_length_line_at {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {ret s r v domain p : B256} {n : Nat} {owner : Adr} {S : List B256}
    (ptr : PtrMem p n M)
    (run : Line.Run sevm (St b
      (p :: 64 :: 66 :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G)
      typedLengthLine d) :
    ∃ G', d = St b
      (p :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S)
      ((M.write p.toNat (66 : B256).toBytes).write 64 (98 + p).toBytes) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word, ptr.read_self ptr.ge] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  rw [B256.sub_self] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  simp only [B256.add_zero] at run
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  cases run
  exact ⟨_, rfl⟩

theorem typed_length_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {ret s r v domain : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 352 480 M)
    (run : Line.Run sevm (St b
      (352 :: 64 :: 66 :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G)
      typedLengthLine d) :
    ∃ G', d = St b
      (352 :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S)
      ((M.write 352 (66 : B256).toBytes).write 64 (450 : B256).toBytes) G' := by
  exact typed_length_line_at ptr run

def typedHashLine (r0 r1 d0 d1 : UInt8) : List Ninst :=
  [.reg (.dup 0),
   .reg .mload,
   .reg (.swap 1),
   .reg .add,
   .reg .keccak256,
   .push [0x00] (by decide),
   .reg (.swap 0),
   .push [r0, r1] (by simp only [List.length_cons, List.length_nil]; decide),
   .reg (.dup 1),
   .reg (.dup 7),
   .reg (.dup 7),
   .reg (.dup 7),
   .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem typed_hash_line_at {r0 r1 d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {ret s r v domain hash p q : B256} {n : Nat} {owner : Adr} {S : List B256}
    (ptr : PtrMem q n M) (length : memWord M p.toNat = 66)
    (lengthFit : p.toNat + 32 ≤ n) (hashFit : (32 + p).toNat + 66 ≤ n)
    (hashRead : (M.read (32 + p).toNat 66).1.keccak = hash)
    (run : Line.Run sevm (St b
      (p :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G)
      (typedHashLine r0 r1 d0 d1) d) :
    ∃ G', d = St b
      ((Bytes.toB256 [d0, d1]) :: s :: r :: v :: hash :: (Bytes.toB256 [r0, r1]) :: hash :: 0 :: 128 ::
       s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M p.toNat :: _) (Mem.read M p.toNat 32).2 _ at state
  rw [length, ptr.read_self lengthFit] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_keccak step
  change _ = St _ ((M.read (32 + p).toNat 66).1.keccak :: _) (Mem.read M (32 + p).toNat 66).2 _ at state
  rw [hashRead, ptr.read_self hashFit] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

theorem typed_hash_line {r0 r1 d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {ret s r v domain hash : B256} {owner : Adr} {S : List B256}
    (ptr : PtrMem 450 480 M) (length : memWord M 352 = 66)
    (hashRead : (M.read 384 66).1.keccak = hash)
    (run : Line.Run sevm (St b
      (352 :: 32 :: 128 :: s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G)
      (typedHashLine r0 r1 d0 d1) d) :
    ∃ G', d = St b
      ((Bytes.toB256 [d0, d1]) :: s :: r :: v :: hash :: (Bytes.toB256 [r0, r1]) :: hash :: 0 :: 128 ::
       s :: r :: v :: domain :: ret :: owner.toB256 :: S) M G' := by
  exact typed_hash_line_at (p := 352) ptr length (by decide) (by decide) hashRead run

/-- The two actual Solidity struct widths share the same overlapping66-byte encoding. -/
theorem typed_memory_facts_at {p : B256} {M : Mem} {domain hash : B256}
    (layout : p = 352 ∨ p = 384) (ptr : PtrMem p p.toNat M) :
    PtrMem p (p.toNat + 128) (typedWordsAt p M domain hash) ∧
    PtrMem (98 + p) (p.toNat + 128) (typedMemoryAt p M domain hash) ∧
    memWord (typedMemoryAt p M domain hash) p.toNat = 66 ∧
    ((typedMemoryAt p M domain hash).read (32 + p).toNat 66).1 =
      ([0x19, 0x01] ++ domain.toBytes ++ hash.toBytes : Bytes) := by
  have lower : 96 ≤ p.toNat := by rcases layout with rfl | rfl <;> decide
  have p1 : PtrMem p (p.toNat + 128) (typedWordsAt p M domain hash) := by
    have staged := ((ptr.write (32 + p).toNat
      (0x1901000000000000000000000000000000000000000000000000000000000000 : B256)
      (.inr (by rcases layout with rfl | rfl <;> decide))).write (34 + p).toNat domain
      (.inr (by rcases layout with rfl | rfl <;> decide))).write (66 + p).toNat hash
      (.inr (by rcases layout with rfl | rfl <;> decide))
    rcases layout with rfl | rfl <;> exact staged
  have written : PtrMem p (p.toNat + 128)
      ((typedWordsAt p M domain hash).write p.toNat (66 : B256).toBytes) := by
    have staged := p1.write p.toNat 66 (.inr lower)
    rw [memExtSize_of_le p1.n32 (by omega)] at staged
    exact staged
  have p2 := written.set (q := 98 + p)
  refine ⟨p1,p2,?_,?_⟩
  · unfold typedMemoryAt
    rw [memWord_congr (μ := (typedWordsAt p M domain hash).write p.toNat (66 : B256).toBytes)
      (fun j hj => (Mem.write_agree _ 64 (98 + p).toBytes).2 (p.toNat + j)
        (by rw [written.size]; omega) (by rw [B256.length_toBytes]; omega))]
    exact (Mem.memWord_write_word _ p.toNat 66).1
  · have image := (Mem.reads_data M).write ptr.wf (32 + p).toNat
      (0x1901000000000000000000000000000000000000000000000000000000000000 : B256).toBytes
    have wf := ptr.wf.write (32 + p).toNat
      (0x1901000000000000000000000000000000000000000000000000000000000000 : B256).toBytes
    have image := image.write wf (34 + p).toNat domain.toBytes
    have wf := wf.write (34 + p).toNat domain.toBytes
    have image := image.write wf (66 + p).toNat hash.toBytes
    have wf := wf.write (66 + p).toNat hash.toBytes
    have image := image.write wf p.toNat (66 : B256).toBytes
    have wf := wf.write p.toNat (66 : B256).toBytes
    have image := image.write wf 64 (98 + p).toBytes
    unfold typedMemoryAt typedWordsAt
    rw [Mem.Reads.read image,
      Bytes.sliceD_writeAt_word_after _ 64 (32 + p).toNat 66 (98 + p)
        (by rcases layout with rfl | rfl <;> decide),
      Bytes.sliceD_writeAt_word_after _ p.toNat (32 + p).toNat 66 66
        (by rcases layout with rfl | rfl <;> decide),
      Bytes.sliceD_writeAt_word_last _ (32 + p).toNat 34 (66 + p).toNat 66 hash
        (by rcases layout with rfl | rfl <;> rfl) rfl,
      Bytes.sliceD_writeAt_word_last _ (32 + p).toNat 2 (34 + p).toNat 34 domain
        (by rcases layout with rfl | rfl <;> rfl) rfl,
      Bytes.sliceD_writeAt_inside _ _ (32 + p).toNat (32 + p).toNat 2 (by omega)
        (by rw [B256.length_toBytes]; omega), Nat.sub_self]
    rfl

theorem typed_memory_facts {M : Mem} {domain hash : B256}
    (ptr : PtrMem 352 352 M) :
    PtrMem 352 480 (typedWords M domain hash) ∧
    PtrMem 450 480 (typedMemory M domain hash) ∧
    memWord (typedMemory M domain hash) 352 = 66 ∧
    ((typedMemory M domain hash).read 384 66).1 =
      ([0x19, 0x01] ++ domain.toBytes ++ hash.toBytes : Bytes) := by
  exact typed_memory_facts_at (Or.inl rfl) ptr

def lowSLine (d0 d1 : UInt8) : List Ninst :=
  [.push [0x00] (by decide),
   .push [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x5d, 0x57, 0x6e, 0x73, 0x57, 0xa4, 0x50, 0x1d, 0xdf, 0xe9, 0x2f, 0x46, 0x68, 0x1b, 0x20, 0xa0] (by decide),
   .reg (.dup 2),
   .reg .gt,
   .reg .iszero,
   .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem lows_line {d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v : B256} {S : List B256}
    (run : Line.Run sevm (St b (s :: r :: v :: S) M G) (lowSLine d0 d1) d) :
    ∃ G', d = St b ((Bytes.toB256 [d0, d1]) :: B256.eqCheck (B256.gtCheck s
        (0x7fffffffffffffffffffffffffffffff5d576e7357a4501ddfe92f46681b20a0 : B256)) 0 :: 0 :: s :: r :: v :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

def v27Line (d0 d1 : UInt8) : List Ninst :=
  [.reg (.dup 3),
   .push [0xff] (by decide),
   .reg .and,
   .push [0x1b] (by decide),
   .reg .eq,
   .reg .iszero,
   .reg (.dup 0),
   .reg .iszero,
   .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem v27_line {d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v : B256} {S : List B256}
    (run : Line.Run sevm (St b (0 :: s :: r :: v :: S) M G) (v27Line d0 d1) d) :
    ∃ G', d = St b ((Bytes.toB256 [d0, d1]) :: B256.eqCheck (B256.eqCheck (B256.eqCheck 27 (255 &&& v)) 0) 0 :: B256.eqCheck (B256.eqCheck 27 (255 &&& v)) 0 :: 0 :: s :: r :: v :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

def v28Line : List Ninst :=
  [.reg .pop,
   .reg (.dup 3),
   .push [0xff] (by decide),
   .reg .and,
   .push [0x1c] (by decide),
   .reg .eq,
   .reg .iszero]

theorem v28_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {s r v : B256} {S : List B256}
    {flag : B256}
    (run : Line.Run sevm (St b (flag :: 0 :: s :: r :: v :: S) M G) v28Line d) :
    ∃ G', d = St b ((B256.eqCheck (B256.eqCheck 28 (255 &&& v)) 0) :: 0 :: s :: r :: v :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  cases run
  exact ⟨_, rfl⟩

def decodeAuthorizationLine (d0 d1 : UInt8) : List Ninst :=
  [.reg .pop,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup 1),
   .reg .calldataload,
   .reg (.dup 1),
   .reg .and,
   .reg (.swap 1),
   .push [0x20] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .and,
   .reg (.swap 0),
   .push [0x40] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0x60] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0x80] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0xa0] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0xff] (by decide),
   .push [0xc0] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg .calldataload,
   .reg .and,
   .reg (.swap 0),
   .push [0xe0] (by decide),
   .reg (.dup 1),
   .reg .add,
   .reg .calldataload,
   .reg (.swap 0),
   .push [0x01, 0x00] (by decide),
   .reg .add,
   .reg .calldataload,
   .push [d0, d1] (by simp only [List.length_cons, List.length_nil]; decide)]

theorem decode_authorization_line {d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {available : B256} {S : List B256}
    (run : Line.Run sevm (St b (available :: 4 :: S) M G) (decodeAuthorizationLine d0 d1) d) :
    ∃ G', d = St b
      ((Bytes.toB256 [d0, d1]) :: Sevm.dataWord sevm 260 :: Sevm.dataWord sevm 228 ::
        (Sevm.dataWord sevm 196 &&& 255) :: Sevm.dataWord sevm 164 ::
        Sevm.dataWord sevm 132 :: Sevm.dataWord sevm 100 :: Sevm.dataWord sevm 68 ::
        (Sevm.dataWord sevm 36).toAdr.toB256 :: (Sevm.dataWord sevm 4).toAdr.toB256 ::
        S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  simp only [ff20_and_word]
  exact ⟨_, rfl⟩


/-- A selector comparison's exact four-instruction prefix. -/
def compareLine (op : Rinst) (c0 c1 c2 c3 d0 d1 : UInt8) : List Ninst :=
  [.reg (.dup 0), .push [c0,c1,c2,c3] (by simp only [List.length_cons,List.length_nil]; decide),
   .reg op, .push [d0,d1] (by simp only [List.length_cons,List.length_nil]; decide)]

theorem compare_gt_line {c0 c1 c2 c3 d0 d1 : UInt8} {sevm : Sevm}
    {b d : Devm} {M : Mem} {G : Nat} {sel : B256} {S : List B256}
    (run : Line.Run sevm (St b (sel :: S) M G)
      (compareLine .gt c0 c1 c2 c3 d0 d1) d) :
    ∃ G', d = St b (Bytes.toB256 [d0,d1] ::
      B256.gtCheck (Bytes.toB256 [c0,c1,c2,c3]) sel :: sel :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

theorem compare_eq_line {c0 c1 c2 c3 d0 d1 : UInt8} {sevm : Sevm}
    {b d : Devm} {M : Mem} {G : Nat} {sel : B256} {S : List B256}
    (run : Line.Run sevm (St b (sel :: S) M G)
      (compareLine .eq c0 c1 c2 c3 d0 d1) d) :
    ∃ G', d = St b (Bytes.toB256 [d0,d1] ::
      B256.eqCheck (Bytes.toB256 [c0,c1,c2,c3]) sel :: sel :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

/-- Success excludes the zero branch when its actual source subtree has no success. -/
theorem guardSucc {code : ByteArray} {c : Cert} {F : Exec.Deriv} {post b : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} {f g : SFunc} {target flag : B256}
    (cut : CursorStateAt code c F (.branch f g) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (dead : f.noOk = true)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    flag ≠ 0 ∧ Nonempty (CursorStateAt code c F g b S M K) := by
  obtain ⟨gas, actual⟩ := cut.state
  obtain ⟨outcome, run⟩ := cut.placed.sourceRun checked (cut.exn_eq.trans success)
    (by rw [cut.sevm_eq]; exact fork)
  rw [cut.tree, actual, cut.sevm_eq] at run
  have nonzero : flag ≠ 0 := by
    rcases rpw_branch run with ⟨_, _, rejected⟩ | ⟨taken, _, _⟩
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk dead).elim
    · exact taken
  exact ⟨nonzero, cut.branchSucc checked success fork nonzero⟩

theorem selector_gt_zero {code : ByteArray} {c : Cert} {F : Exec.Deriv} {post b : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} {f g : SFunc}
    {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8}
    (cut : CursorStateAt code c F
      ((compareLine .gt c0 c1 c2 c3 d0 d1).foldr SFunc.next (.branch f g)) b (sel :: S) M K)
    (checked : Cert.check code c = true)
    (zero : B256.gtCheck (Bytes.toB256 [c0,c1,c2,c3]) sel = 0)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c F f b (sel :: S) M K) := by
  obtain ⟨tested⟩ := cut.line checked success fork _ rfl
    (by intro ni member xi same; subst ni
        simp only [compareLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    compare_gt_line
  rw [zero] at tested
  exact tested.branchZero checked success fork

theorem selector_gt_succ {code : ByteArray} {c : Cert} {F : Exec.Deriv} {post b : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} {f g : SFunc}
    {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8}
    (cut : CursorStateAt code c F
      ((compareLine .gt c0 c1 c2 c3 d0 d1).foldr SFunc.next (.branch f g)) b (sel :: S) M K)
    (checked : Cert.check code c = true)
    (nonzero : B256.gtCheck (Bytes.toB256 [c0,c1,c2,c3]) sel ≠ 0)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c F g b (sel :: S) M K) := by
  obtain ⟨tested⟩ := cut.line checked success fork _ rfl
    (by intro ni member xi same; subst ni
        simp only [compareLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    compare_gt_line
  exact tested.branchSucc checked success fork nonzero

theorem selector_eq_zero {code : ByteArray} {c : Cert} {F : Exec.Deriv} {post b : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} {f : SFunc} {k : Nat}
    {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8}
    (cut : CursorStateAt code c F
      ((compareLine .eq c0 c1 c2 c3 d0 d1).foldr SFunc.next (.branchTo f k)) b (sel :: S) M K)
    (checked : Cert.check code c = true)
    (zero : B256.eqCheck (Bytes.toB256 [c0,c1,c2,c3]) sel = 0)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c F f b (sel :: S) M K) := by
  obtain ⟨tested⟩ := cut.line checked success fork _ rfl
    (by intro ni member xi same; subst ni
        simp only [compareLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    compare_eq_line
  rw [zero] at tested
  exact tested.toZero checked success fork

theorem selector_eq_succ {code : ByteArray} {c : Cert} {F : Exec.Deriv} {post b : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} {f g : SFunc} {k : Nat}
    {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8}
    (cut : CursorStateAt code c F
      ((compareLine .eq c0 c1 c2 c3 d0 d1).foldr SFunc.next (.branchTo f k)) b (sel :: S) M K)
    (checked : Cert.check code c = true)
    (nonzero : B256.eqCheck (Bytes.toB256 [c0,c1,c2,c3]) sel ≠ 0)
    (lookup : c.prog[k]? = some g)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code c F g b (sel :: S) M K) := by
  obtain ⟨tested⟩ := cut.line checked success fork _ rfl
    (by intro ni member xi same; subst ni
        simp only [compareLine,List.mem_cons,List.not_mem_nil,reduceCtorEq,or_self] at member)
    compare_eq_line
  exact tested.toSucc checked success fork nonzero lookup

/-- A failed taken branch is excluded by the original success. -/
theorem guardZero {code : ByteArray} {c : Cert} {F : Exec.Deriv} {post b : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} {f g : SFunc} {target flag : B256}
    (cut : CursorStateAt code c F (.branch f g) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (dead : g.noOk = true)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    flag = 0 ∧ Nonempty (CursorStateAt code c F f b S M K) := by
  obtain ⟨gas, actual⟩ := cut.state
  obtain ⟨outcome, run⟩ := cut.placed.sourceRun checked (cut.exn_eq.trans success)
    (by rw [cut.sevm_eq]; exact fork)
  rw [cut.tree, actual, cut.sevm_eq] at run
  have zero : flag = 0 := by
    rcases rpw_branch run with ⟨taken, _, _⟩ | ⟨_, _, rejected⟩
    · exact taken
    · exact ((SFunc.runP_iff_runCutP_nil.mp rejected).false_of_noOk dead).elim
  rw [zero] at cut
  exact ⟨zero, cut.branchZero checked success fork⟩

/-- The actual first calldata word produces its selector prefix. -/
def selectorLine : List Ninst :=
  [.push [0] (by decide), .reg .calldataload, .push [0xe0] (by decide), .reg .shr]

theorem selector_line {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    (run : Line.Run sevm (St b S M G) selectorLine d) :
    ∃ G', d = St b (Sevm.selector sevm :: S) M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldataload step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_shr step
  cases run
  exact ⟨_, rfl⟩

/-- The ABI wrapper's actual subtraction/length-guard prefix. -/
def wrapperLine (r0 r1 : UInt8) (width : Bytes) (le : width.length ≤ 32)
    (d0 d1 : UInt8) : List Ninst :=
  [.push [r0,r1] (by simp only [List.length_cons,List.length_nil]; decide),
   .push [4] (by decide), .reg (.dup 0), .reg .calldatasize, .reg .sub,
   .push width le, .reg (.dup 1), .reg .lt, .reg .iszero,
   .push [d0,d1] (by simp only [List.length_cons,List.length_nil]; decide)]

theorem wrapper_line {r0 r1 d0 d1 : UInt8} {width : Bytes} {le : width.length ≤ 32}
    {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat} {sel : B256}
    (run : Line.Run sevm (St b [sel] M G) (wrapperLine r0 r1 width le d0 d1) d) :
    ∃ G', d = St b
      [Bytes.toB256 [d0,d1], B256.eqCheck
        (B256.ltCheck (sevm.data.length.toB256 - 4) (Bytes.toB256 width)) 0,
       sevm.data.length.toB256 - 4, 4, Bytes.toB256 [r0,r1], sel] M G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_calldatasize step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_lt step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_, rfl⟩

/-- Seven ordered ABI words; the source type word remains an explicit instruction parameter. -/
def sevenWordHash (tag : B256) (owner spender : Adr)
    (value validAfter validBefore nonce : B256) : B256 :=
  (tag.toBytes ++ owner.toB256.toBytes ++ spender.toB256.toBytes ++ value.toBytes ++
    validAfter.toBytes ++ validBefore.toBytes ++ nonce.toBytes).keccak

def sevenWordBodyMemory (M : Mem) (spender : Adr)
    (value validAfter validBefore nonce : B256) : Mem :=
  ((((M.write 224 spender.toB256.toBytes).write 256 value.toBytes).write
    288 validAfter.toBytes).write 320 validBefore.toBytes).write 352 nonce.toBytes

def sevenWordMemory (tag : B256) (M : Mem) (owner spender : Adr)
    (value validAfter validBefore nonce : B256) : Mem :=
  let M := structHeadMemory tag M owner
  let M := sevenWordBodyMemory M spender value validAfter validBefore nonce
  (M.write 128 (224 : B256).toBytes).write 64 (384 : B256).toBytes

def sevenWordHeadLine (tag : Bytes) (le : tag.length ≤ 32) : List Ninst :=
  [.push [0x40] (by decide),
   .reg (.dup 0),
   .reg .mload,
   .push tag le,
   .push [0x20] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg .mstore,
   .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
   .reg (.dup 0),
   .reg (.dup 12),
   .reg .and,
   .reg (.dup 2),
   .reg (.dup 4),
   .reg .add,
   .reg (.dup 1),
   .reg (.swap 0),
   .reg .mstore]

theorem seven_word_head_line {tag : Bytes} {le : tag.length ≤ 32}
    {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {nonce validBefore validAfter value s r v : B256} {owner spender : Adr} {S : List B256}
    (ptr : PtrMem 128 96 M)
    (run : Line.Run sevm (St b (s :: r :: v :: nonce :: validBefore :: validAfter :: value :: spender.toB256 :: owner.toB256 :: S) M G)
      (sevenWordHeadLine tag le) d) :
    ∃ G', d = St b
      (owner.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff : B256) :: 128 :: 64 ::
        s :: r :: v :: nonce :: validBefore :: validAfter :: value :: spender.toB256 :: owner.toB256 :: S)
      (structHeadMemory (Bytes.toB256 tag) M owner) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word,ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_and step
  rw [B256.and_comm,ff20_and_word,toAdr_toB256] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  cases run
  exact ⟨_,rfl⟩

def sevenWordBodyLine : List Ninst :=
  [.reg (.swap 0),
   .reg (.dup 11),
   .reg .and,
   .push [0x60] (by decide),
   .reg (.dup 3),
   .reg .add,
   .reg .mstore,
   .push [0x80] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg (.dup 10),
   .reg (.swap 0),
   .reg .mstore,
   .push [0xa0] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg (.dup 9),
   .reg (.swap 0),
   .reg .mstore,
   .push [0xc0] (by decide),
   .reg (.dup 2),
   .reg .add,
   .reg (.dup 8),
   .reg (.swap 0),
   .reg .mstore,
   .push [0xe0] (by decide),
   .reg (.dup 0),
   .reg (.dup 3),
   .reg .add,
   .reg (.dup 8),
   .reg (.swap 0),
   .reg .mstore]

theorem seven_word_body_line {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {nonce validBefore validAfter value s r v : B256} {owner spender : Adr} {S : List B256}
    (run : Line.Run sevm (St b
      (owner.toB256 :: (0xffffffffffffffffffffffffffffffffffffffff : B256) :: 128 :: 64 ::
        s :: r :: v :: nonce :: validBefore :: validAfter :: value :: spender.toB256 :: owner.toB256 :: S) M G) sevenWordBodyLine d) :
    ∃ G', d = St b (224 :: owner.toB256 :: 128 :: 64 :: s :: r :: v :: nonce :: validBefore :: validAfter :: value :: spender.toB256 :: owner.toB256 :: S)
      (sevenWordBodyMemory M spender value validAfter validBefore nonce) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_and step
  have canonical : (spender.toB256 &&& (0xffffffffffffffffffffffffffffffffffffffff : B256)) = spender.toB256 := by
    change (spender.toB256 &&& Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff]) = _
    rw [B256.and_comm,ff20_and_word,toAdr_toB256]
  rw [canonical] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  cases run
  exact ⟨_,rfl⟩

def sevenWordTailLine (slot r0 r1 d0 d1 : UInt8) : List Ninst :=
  [.reg (.dup 3),
   .reg .mload,
   .reg (.dup 0),
   .reg (.dup 4),
   .reg .sub,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg .add,
   .reg (.dup 1),
   .reg .mstore,
   .push [0x01, 0x00] (by decide),
   .reg (.swap 0),
   .reg (.swap 2),
   .reg .add,
   .reg (.swap 0),
   .reg (.swap 2),
   .reg .mstore,
   .push [slot] (by simp only [List.length_cons,List.length_nil]; decide),
   .reg .sload,
   .reg (.swap 0),
   .reg (.swap 1),
   .reg (.swap 0),
   .push [r0,r1] (by simp only [List.length_cons,List.length_nil]; decide),
   .reg (.swap 0),
   .reg (.dup 6),
   .reg (.dup 6),
   .reg (.dup 6),
   .reg (.dup 6),
   .push [d0,d1] (by simp only [List.length_cons,List.length_nil]; decide)]

theorem seven_word_tail_line {slot r0 r1 d0 d1 : UInt8}
    {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {nonce validBefore validAfter value s r v : B256} {owner spender : Adr} {S : List B256}
    (ptr : PtrMem 128 384 M) (fork : CoveredFork sevm.benvStat.fork)
    (run : Line.Run sevm (St b
      (224 :: owner.toB256 :: 128 :: 64 :: s :: r :: v :: nonce :: validBefore :: validAfter :: value :: spender.toB256 :: owner.toB256 :: S) M G)
      (sevenWordTailLine slot r0 r1 d0 d1) d) :
    ∃ G', d = St (afterSload sevm b (Bytes.toB256 [slot]))
      (Bytes.toB256 [d0,d1] :: 128 :: s :: r :: v ::
        b.getStorVal sevm.currentTarget (Bytes.toB256 [slot]) :: Bytes.toB256 [r0,r1] ::
        owner.toB256 :: 128 :: s :: r :: v :: nonce :: validBefore :: validAfter :: value :: spender.toB256 :: owner.toB256 :: S)
      ((M.write 128 (224 : B256).toBytes).write 64 (384 : B256).toBytes) G' := by
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, state⟩ := ri_mload step
  change _ = St _ (memWord M 64 :: _) (Mem.read M 64 32).2 _ at state
  rw [ptr.word,ptr.read_self (by decide)] at state
  subst state
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_mstore step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, run⟩ := Line.of_run_cons run
  obtain ⟨_, rfl⟩ := ri_push step
  cases run
  exact ⟨_,rfl⟩

theorem seven_word_memory_facts {tag : B256} {M : Mem} {owner spender : Adr}
    {value validAfter validBefore nonce : B256} (ptr : PtrMem 128 96 M) :
    PtrMem 384 384 (sevenWordMemory tag M owner spender value validAfter validBefore nonce) ∧
    memWord (sevenWordMemory tag M owner spender value validAfter validBefore nonce) 128 = 224 ∧
    ((sevenWordMemory tag M owner spender value validAfter validBefore nonce).read 160 224).1.keccak =
      sevenWordHash tag owner spender value validAfter validBefore nonce := by
  have p1 := (ptr.write 160
    (tag : B256)
    (.inr (by decide))).write 192 owner.toB256 (.inr (by decide))
  have p2 := (((p1.write 224 spender.toB256 (.inr (by decide))).write 256 value
    (.inr (by decide))).write 288 validAfter (.inr (by decide))).write 320 validBefore (.inr (by decide))
  have p2 := p2.write 352 nonce (.inr (by decide))
  have p3 := (p2.write 128 224 (.inr (by decide))).set (q := 384)
  refine ⟨p3, ?_, ?_⟩
  · unfold sevenWordMemory
    rw [memWord_congr (μ := (sevenWordBodyMemory (structHeadMemory tag M owner) spender value validAfter validBefore nonce).write 128 (224 : B256).toBytes)
      (fun j hj => ?_)]
    · exact (Mem.memWord_write_word _ 128 224).1
    · exact (Mem.write_agree _ 64 (384 : B256).toBytes).2 (128 + j)
        (by
          have hs : ((sevenWordBodyMemory (structHeadMemory tag M owner) spender value validAfter validBefore nonce).write
            128 (224 : B256).toBytes).size = 384 := (p2.write 128 224 (.inr (by decide))).size
          rw [hs]
          omega)
        (by rw [B256.length_toBytes]; omega)
  · have image := (Mem.reads_data M).write ptr.wf 160
      (tag : B256).toBytes
    have wf := ptr.wf.write 160
      (tag : B256).toBytes
    have image := image.write wf 192 owner.toB256.toBytes
    have wf := wf.write 192 owner.toB256.toBytes
    have image := image.write wf 224 spender.toB256.toBytes
    have wf := wf.write 224 spender.toB256.toBytes
    have image := image.write wf 256 value.toBytes
    have wf := wf.write 256 value.toBytes
    have image := image.write wf 288 validAfter.toBytes
    have wf := wf.write 288 validAfter.toBytes
    have image := image.write wf 320 validBefore.toBytes
    have wf := wf.write 320 validBefore.toBytes
    have image := image.write wf 352 nonce.toBytes
    have wf := wf.write 352 nonce.toBytes
    have image := image.write wf 128 (224 : B256).toBytes
    have wf := wf.write 128 (224 : B256).toBytes
    have image := image.write wf 64 (384 : B256).toBytes
    unfold sevenWordMemory sevenWordBodyMemory structHeadMemory
    rw [Mem.Reads.read image,
      Bytes.sliceD_writeAt_word_after _ 64 160 224 384 (by decide),
      Bytes.sliceD_writeAt_word_after _ 128 160 224 224 (by decide),
      Bytes.sliceD_writeAt_word_last _ 160 192 352 224 nonce rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 160 320 192 validBefore rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 128 288 160 validAfter rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 96 256 128 value rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 64 224 96 spender.toB256 rfl rfl,
      Bytes.sliceD_writeAt_word_last _ 160 32 192 64 owner.toB256 rfl rfl,
      sliceD_word_same]
    rfl

/-- Canonical native-address word compared with an actual caller word. -/
def maskedOwnerLine (d0 d1 : UInt8) : List Ninst :=
  [.push [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
    0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] (by decide),
   .reg .and,.reg .eq,.push [d0,d1] (by simp only [List.length_cons,List.length_nil]; decide)]

theorem masked_owner_line {d0 d1 : UInt8} {sevm : Sevm} {b d : Devm} {M : Mem} {G : Nat}
    {answer : Adr} {owner : B256} {S : List B256}
    (run : Line.Run sevm (St b (answer.toB256 :: owner :: S) M G)
      (maskedOwnerLine d0 d1) d) :
    ∃ G', d = St b (Bytes.toB256 [d0,d1] :: B256.eqCheck answer.toB256 owner :: S) M G' := by
  obtain ⟨_,step,run⟩ := Line.of_run_cons run
  obtain ⟨_,rfl⟩ := ri_push step
  obtain ⟨_,step,run⟩ := Line.of_run_cons run
  obtain ⟨_,state⟩ := ri_and step
  rw [ff20_and_word,toAdr_toB256] at state
  subst state
  obtain ⟨_,step,run⟩ := Line.of_run_cons run
  obtain ⟨_,rfl⟩ := ri_eq step
  obtain ⟨_,step,run⟩ := Line.of_run_cons run
  obtain ⟨_,rfl⟩ := ri_push step
  cases run
  exact ⟨_,rfl⟩

/-- An actual successful checked branch also records the decoded target PC. -/
theorem guardSucc_pc {code : ByteArray} {c : Cert} {F : Exec.Deriv} {post b : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} {f g : SFunc} {target flag : B256}
    (cut : CursorStateAt code c F (.branch f g) b (target :: flag :: S) M K)
    (checked : Cert.check code c = true) (dead : f.noOk = true)
    (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork) :
    flag ≠ 0 ∧ ∃ reached : CursorStateAt code c F g b S M K, reached.node.pc = target.toNat := by
  obtain ⟨taken,_⟩ := guardSucc cut checked dead success fork
  obtain ⟨gas,actualState⟩ := cut.state
  have decoded := cut.placed.jumpiAt_of_branch cut.tree
  obtain ⟨N,next,edge,jumped,_,stateful,placed⟩ := cursor_jinst_forward checked cut.placed decoded
    (cut.exn_eq.trans success) (by rw [cut.sevm_eq]; exact fork)
  have actualStep : ConfStep (Ninst.RunWith (Cursor.DescOf cut.node)) c.prog F.sevm
      ⟨St b (target :: flag :: S) M gas,.branch f g,K⟩
      ⟨N.devm,next.f,next.K.map Cont.f⟩ := by
    simpa only [Cursor.conf,cut.sevm_eq,actualState,cut.tree,cut.continuations] using stateful
  have shape : next.f = g ∧ next.K.map Cont.f = K ∧ ∃ G', N.devm = St b S M G' := by
    generalize hf : next.f = f' at actualStep ⊢
    generalize hk : next.K.map Cont.f = K' at actualStep ⊢
    generalize hd : N.devm = d' at actualStep ⊢
    cases actualStep with
    | zero _ pop => exact (taken (St.of_pop2 pop).2.1).elim
    | succ _ _ _ pop => exact ⟨rfl,rfl,_,(St.of_pop2 pop).2.2⟩
  have actualPc : N.pc = target.toNat := by
    rcases of_jumpi_run jumped with ⟨x,_,pop⟩ | ⟨x,y,nextPc,pop,_,_⟩
    · rw [actualState] at pop
      exact (taken (St.of_pop2 pop).2.1).elim
    · rw [actualState] at pop
      rw [← (St.of_pop2 pop).1] at nextPc
      exact nextPc
  have sameExn : N.exn = cut.node.exn := by
    generalize origin : cut.node = D at edge ⊢
    cases edge <;> rfl
  exact ⟨taken,⟨N,next,cut.free.trans (Exec.Deriv.ExecFreeUntil.ofStep edge
    (Blanc.Jinst.At.not_exec decoded)),(Cursor.parentStep_sevm edge).trans cut.sevm_eq,
    sameExn.trans cut.exn_eq,placed,shape.1,shape.2.2,shape.2.1⟩,actualPc⟩

end Blanc.Lift.SolcSignedQuery
