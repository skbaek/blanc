import Blanc.Lift.Curve3Pool.Walk.Kit
import Blanc.Lift.VyperDispatchExact

/-!
# The dispatcher, forward and gas-exact

From the entry tree `t_0000_c0` (empty stack and memory) the runtime checks `CALLDATASIZE ≥ 4`
(17 gas), enters `t_000d_c0` (1), runs the Vyper prologue (75) and then the selector chain from
`poolHead`, which `SFunc.vyFwd` evaluates (`Blanc/Lift/VyperDispatchExact.lean`).
`rxe_dispatch` hands a run of the arm the chain reaches for the frame's selector to the entry,
for `100` gas plus the chain's; the kernel computes the arm and the gas (`kernel_rfl`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The first tree after the prologue: the always-taken skip to the first selector test. -/
def poolHead : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg .iszero) (.next (.push [0x02, 0x44] (by decide))
    (.branch .undefined t_0244_c0)))

theorem t_000d_eq : t_000d_c0 = .dest (vyPrologue poolHead) := rfl

/-- **The dispatcher, forward**: with the selector `σ`, a run of the arm `q` the chain hands `σ`
is a run of the entry, for `N` gas more (`N - 100` spent on the chain). -/
theorem rxe_dispatch {sevm : Sevm} {b : Devm} {G N : Nat} {σ : B256} {q : SFunc}
    {Q : Outcome → Prop}
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = σ)
    (hq : SFunc.vyFwd σ 64 poolHead = (q, N - 100)) (hN : 100 ≤ N)
    (k : SFunc.RunEx cert.prog sevm (St b [] (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) q Q) :
    SFunc.RunEx cert.prog sevm (St b [] Mem.empty (G + N)) t_0000_c0 Q := by
  have hlen4 : B256.eqCheck (B256.ltCheck (Nat.toB256 sevm.data.length) (Bytes.toB256 [0x04]))
      0 ≠ 0 := by
    rw [B256.ltCheck_eq_zero_of_toNat_le (by rw [B256.toNat_toB256_of_lt hcd]; exact hlen)]; decide
  have k' := rxe_vyFwd (S := []) hsel (by decide) 64 poolHead (by rw [hq]; exact k)
  rw [hq] at k'
  rw [show G + N = G + (N - 100) + 75 + 1 + 10 + 3 + 3 + 3 + 2 + 3 by omega]
  unfold t_0000_c0
  xr (rx_push rfl (by simp only [List.length_nil]; omega) ·)
  xr (rx_calldatasize (by simp only [List.length_cons, List.length_nil]; omega) ·)
  xr (rx_lt rfl (by simp only [List.length_cons, List.length_nil]; omega) ·)
  xr (rx_iszero rfl (by simp only [List.length_cons, List.length_nil]; omega) ·)
  xr (rx_push rfl (by simp only [List.length_cons, List.length_nil]; omega) ·)
  xr (rx_branch_succ hlen4 ·)
  rw [t_000d_eq]
  xr (rx_dest ·)
  xr (rx_vyPrologue (by simp only [List.length_nil]; omega) ·)
  exact k'

end Blanc.Lift.Curve3Pool
