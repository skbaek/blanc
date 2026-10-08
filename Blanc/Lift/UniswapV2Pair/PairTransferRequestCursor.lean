import Blanc.Lift.UniswapV2Pair.PairTransferCursor
import Blanc.Lift.UniswapV2Pair.PairTransferCopyCursor
import Blanc.Lift.UniswapV2Pair.PairTransferCallCursor

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The original moving initializer, both copy passes and partial merge reach
this actual GAS cursor with the exact 68-byte transfer payload. -/
theorem pair_transfer_request_cursor_state {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (cut : CursorStateAt code cert start t_1fdb_c57 b
      (amount :: toWord :: tokenWord :: rho :: R) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    let V := safeTransfer_dynamicCallMemory M p amount toWord
    PtrMem (p + 164) V.size V ∧ Nonempty (CursorStateAt code cert start pairTransferGasTree b
      ((tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 0 ::
        (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) V K) := by
  let P := safeTransfer_dynamicPayloadMemory M p amount toWord
  let C1 := P.write (p + 164).toNat (Bytes.toB256 (P.read (p + 96).toNat 32).1).toBytes
  let C2 := C1.write (p + 196).toNat (Bytes.toB256 (C1.read (p + 128).toNat 32).1).toBytes
  let V := safeTransfer_dynamicCallMemory M p amount toWord
  obtain ⟨adv96, adv128, adv164, adv196, length68⟩ := safeTransfer_stageAdvance width
  have read96 := safeTransfer_copyRead96 (amount := amount) (toWord := toWord) mem lower width
  have read128 := safeTransfer_copyRead128 (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨payloadMem, ⟨copy⟩⟩ := pair_transfer_initialize_cursor_state cut success fork mem lower width
  obtain ⟨remaining⟩ := pair_transfer_copy68_cursor_state copy success fork
  rw [read96, adv96, adv128, adv164, adv196, read128] at remaining
  have addNat (k : Nat) (bound : k ≤ 260) : (p + k.toB256).toNat = p.toNat + k := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    simpa only [show (164 : Nat).toB256 = (164 : B256) from rfl] using addNat 164 (by decide)
  have nat196 : (p + 196).toNat = p.toNat + 196 := by
    simpa only [show (196 : Nat).toB256 = (196 : B256) from rfl] using addNat 196 (by decide)
  have nat160 : (p + 160).toNat = p.toNat + 160 := by
    simpa only [show (160 : Nat).toB256 = (160 : B256) from rfl] using addNat 160 (by decide)
  have c1Mem := payloadMem.write (p + 164).toNat (Bytes.toB256 (P.read (p + 96).toNat 32).1)
    (Or.inr (by rw [nat164]; omega))
  have c2Mem := c1Mem.write (p + 196).toNat (Bytes.toB256 (C1.read (p + 128).toNat 32).1)
    (Or.inr (by rw [nat196]; omega))
  have fit160 : (p + 160).toNat + 32 ≤
      memExtSize (memExtSize P.size (p + 164).toNat 32) (p + 196).toNat 32 := by
    have bound := memExtSize_access_le
      (memExtSize P.size (p + 164).toNat 32) (p + 196).toNat 32 (by decide)
    rw [nat160, nat196] at *
    omega
  have callMem := safeTransfer_callMemory_ptr (amount := amount) (toWord := toWord) mem lower width
  have sameMemory := safeTransfer_callMemory_eq (M := M) (amount := amount) (toWord := toWord) width
  dsimp only at sameMemory
  obtain ⟨opened⟩ := remaining.dest cert_check success fork
  obtain ⟨gas⟩ := opened.line cert_check success fork pairTransferPartialLine rfl
    (by intro inst member x equal; subst inst; simp only [pairTransferPartialLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (S' := (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 0 ::
      (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
    (M' := V) (by
      intro G d line
      have raw := pair_transfer_partial_line_inv line
      dsimp only at raw
      change ∃ residual, d = St b
        ((tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 0 ::
          Bytes.toB256 _ :: _ :: Bytes.toB256 _ :: 0 :: (68 + (p + 164)) ::
          (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) _ residual at raw
      rw [show (C2.read (p + 160).toNat 32).2 = C2 from c2Mem.read_self fit160,
        sameMemory] at raw
      have pointer : Bytes.toB256 (V.read 64 32).1 = p + 164 := callMem.word
      rw [pointer, callMem.read_self callMem.ge, length68] at raw
      exact raw)
  exact ⟨callMem, ⟨gas⟩⟩

end Blanc.Lift.UniswapV2Pair
