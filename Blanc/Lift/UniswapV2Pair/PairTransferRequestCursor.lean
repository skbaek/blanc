import Blanc.Lift.UniswapV2Pair.PairTransferCursor
import Blanc.Lift.UniswapV2Pair.PairTransferCopyCursor
import Blanc.Lift.UniswapV2Pair.PairTransferCallCursor

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The two full copy writes, before the final partial-word merge. -/
def pairTransferCopiedMemory (M : Mem) (p amount toWord : B256) : Mem :=
  let P := safeTransfer_dynamicPayloadMemory M p amount toWord
  let C1 := P.write (p + 164).toNat (Bytes.toB256 (P.read (p + 96).toNat 32).1).toBytes
  C1.write (p + 196).toNat (Bytes.toB256 (C1.read (p + 128).toNat 32).1).toBytes

/-- The partial merge's complete state normalization, independent of final
success and fork selection. Shared by the historical cursor and raw control wrappers. -/
theorem pair_transfer_partial_line_state {sevm : Sevm} {b d : Devm}
    {R : List B256} {M : Mem} {G : Nat}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (line : Line.Run sevm (St b
      ((p + 160) :: (p + 228) :: 4 :: 68 :: (p + 96) :: (p + 164) ::
        (p + 164) :: (p + 64) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
      (pairTransferCopiedMemory M p amount toWord) G) pairTransferPartialLine d) :
    ∃ residual, d = St b
      ((tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 0 ::
        (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
      (safeTransfer_dynamicCallMemory M p amount toWord) residual := by
  let P := safeTransfer_dynamicPayloadMemory M p amount toWord
  let C1 := P.write (p + 164).toNat (Bytes.toB256 (P.read (p + 96).toNat 32).1).toBytes
  let C2 := C1.write (p + 196).toNat (Bytes.toB256 (C1.read (p + 128).toNat 32).1).toBytes
  let V := safeTransfer_dynamicCallMemory M p amount toWord
  obtain ⟨_, _, _, payloadMem, _⟩ :=
    safeTransfer_dynamicPayload_facts (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨_, _, _, _, length68⟩ := safeTransfer_stageAdvance width
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
  change Line.Run sevm (St b _ C2 G) pairTransferPartialLine d at line
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
  exact raw

/-- The original moving initializer, both copy passes and partial merge reach
this actual GAS cursor with the exact 68-byte transfer payload. -/
theorem pair_transfer_request_cursor_stateH {start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (cut : CursorStateAt code cert start t_1fdb_c57 b
      (amount :: toWord :: tokenWord :: rho :: R) M K)
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
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
  obtain ⟨payloadMem, ⟨copy⟩⟩ := pair_transfer_initialize_cursor_stateH cut success stateGas mem lower width
  obtain ⟨remaining⟩ := pair_transfer_copy68_cursor_stateH copy success stateGas
  rw [read96, adv96, adv128, adv164, adv196, read128] at remaining
  have callMem := safeTransfer_callMemory_ptr (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨opened⟩ := remaining.destH cert_check success stateGas
  obtain ⟨gas⟩ := opened.lineH cert_check success stateGas pairTransferPartialLine rfl
    (by intro inst member x equal; subst inst; simp only [pairTransferPartialLine,
      List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (pair_transfer_partial_line_state mem lower width)
  exact ⟨callMem, ⟨gas⟩⟩

end Blanc.Lift.UniswapV2Pair
