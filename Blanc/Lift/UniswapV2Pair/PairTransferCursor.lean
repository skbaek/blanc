import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.SafeTransferWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The original initializer advances the supplied actual cursor, retaining its
full world and physical moving payload image before the bounded copy. -/
theorem pair_transfer_initialize_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (cut : CursorStateAt code cert root t_1fdb_c57 b
      (amount :: toWord :: tokenWord :: rho :: R) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    let N := safeTransfer_dynamicPayloadMemory M p amount toWord
    PtrMem (p + 164) N.size N ∧ Nonempty (CursorStateAt code cert root t_20a4_c57 b
      ((p + 96) :: (p + 164) :: 68 :: 68 :: (p + 96) :: (p + 164) ::
        (p + 164) :: (p + 64) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) N K) := by
  obtain ⟨h3, h5, h7, h8, fit7, fit8, read0, read3, read5, read8, length8,
    combine36, combine68, combine100, combine32⟩ :=
    safeTransfer_dynamicPayload_facts (amount := amount) (toWord := toWord) mem lower width
  have nat64 : (p + 64).toNat = p.toNat + 64 := by
    rw [B256.toNat_add, show (64 : B256).toNat = 64 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have nat96 : (p + 96).toNat = p.toNat + 96 := by
    rw [B256.toNat_add, show (96 : B256).toNat = 96 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  have reached := opened.line cert_check success fork pairTransferInitializeLine rfl
    (by intro inst member x equal; subst inst
        simp only [pairTransferInitializeLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    (b' := b)
    (S' := (p + 96) :: (p + 164) :: 68 :: 68 :: (p + 96) :: (p + 164) ::
      (p + 164) :: (p + 64) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
    (M' := safeTransfer_dynamicPayloadMemory M p amount toWord) (by
      intro G d line
      have raw := pair_transfer_initialize_line_inv line
      dsimp only at raw
      simp only [show (64 : B256).toNat = 64 from rfl] at raw
      rw [read0, mem.read_self mem.ge,
        show (64 : B256) + p = p + 64 from B256.add_comm,
        show (32 : B256) + p = p + 32 from B256.add_comm] at raw
      rw [read3, h3.read_self h3.ge, combine36, combine68] at raw
      rw [read5, h5.read_self h5.ge,
        show (68 : B256) + ((p + 64) - (p + 64)) = 68 from by rw [B256.sub_self, B256.add_zero],
        combine100, combine32] at raw
      rw [h7.read_self (by rw [nat96]; omega)] at raw
      rw [read8, h8.read_self h8.ge, length8,
        h8.read_self (by
          have bound : (p + 64).toNat + 32 ≤ p.toNat + 164 := by rw [nat64]; omega
          exact bound.trans fit8)] at raw
      exact raw)
  exact ⟨h8, reached⟩

end Blanc.Lift.UniswapV2Pair
