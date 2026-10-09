import Blanc.Lift.UniswapV2Pair.SwapAbi
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.InvWalkBranchToP

/-! The literal swap body prefix: the lock test and lock store, the output-amount guard,
the internal `getReserves` call, the liquidity guards, the token loads and the recipient
guard, up to the optimistic-transfer branch `t_08bf_c4`. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Literal Swap lockguard line shared by the inverse and original cursor. -/
def swapLockGuardLine : List Ninst := [
  .push [0x0c] (by decide),
  .reg .sload,
  .push [0x01] (by decide),
  .reg .eq,
  .push [0x06, 0xf4] (by decide)]

theorem swapLockGuardLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (line : Line.Run sevm (St b S M G) swapLockGuardLine d) :
    ∃ G', d = St (afterSload sevm b (Bytes.toB256 [0x0c]))
      ((Bytes.toB256 [0x06, 0xf4]) ::
       (B256.eqCheck (Bytes.toB256 [0x01]) (b.getStorVal sevm.currentTarget (Bytes.toB256 [0x0c]))) :: S) M G' := by
  dsimp only [swapLockGuardLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  exact ⟨gas, state⟩

/-- Literal Swap lockstore line shared by the inverse and original cursor. -/
def swapLockStoreLine : List Ninst := [
  .push [0x00] (by decide),
  .push [0x0c] (by decide),
  .reg .sstore,
  .reg (.dup 4),
  .reg .iszero,
  .reg .iszero,
  .reg (.dup 0),
  .push [0x07, 0x07] (by decide)]

theorem swapLockStoreLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {len start toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (line : Line.Run sevm (St b (len :: start :: toWord :: a1 :: a0 :: rho :: S) M G) swapLockStoreLine d) :
    sevm.isStatic = false ∧ ∃ G', d = St (afterSstore sevm b (Bytes.toB256 [0x0c]) (Bytes.toB256 [0x00]))
      ((Bytes.toB256 [0x07, 0x07]) ::
       (B256.eqCheck (B256.eqCheck a0 0) 0) ::
       (B256.eqCheck (B256.eqCheck a0 0) 0) ::
       len ::
       start ::
       toWord ::
       a1 ::
       a0 ::
       rho :: S) M G' := by
  dsimp only [swapLockStoreLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line
  have nonstatic := ri_sstore_nonstatic fork step; obtain ⟨_, rfl⟩ := ri_sstore fork step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  exact ⟨nonstatic, gas, state⟩

/-- Literal Swap outputfallback line shared by the inverse and original cursor. -/
def swapOutputFallbackLine : List Ninst := [
  .reg .pop,
  .push [0x00] (by decide),
  .reg (.dup 4),
  .reg .gt]

theorem swapOutputFallbackLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {flag len start toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (flag :: len :: start :: toWord :: a1 :: a0 :: rho :: S) M G) swapOutputFallbackLine d) :
    ∃ G', d = St b
      ((B256.gtCheck a1 (Bytes.toB256 [0x00])) ::
       len ::
       start ::
       toWord ::
       a1 ::
       a0 ::
       rho :: S) M G' := by
  dsimp only [swapOutputFallbackLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_gt step
  cases line
  exact ⟨gas, state⟩

/-- Literal Swap reservesetup line shared by the inverse and original cursor. -/
def swapReserveSetupLine : List Ninst := [
  .push [0x00] (by decide),
  .reg (.dup 0),
  .push [0x07, 0x67] (by decide),
  .push [0x0d, 0x90] (by decide)]

theorem swapReserveSetupLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b S M G) swapReserveSetupLine d) :
    ∃ G', d = St b
      ((Bytes.toB256 [0x0d, 0x90]) ::
       (Bytes.toB256 [0x07, 0x67]) ::
       (Bytes.toB256 [0x00]) ::
       (Bytes.toB256 [0x00]) :: S) M G' := by
  dsimp only [swapReserveSetupLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  exact ⟨gas, state⟩

/-- Literal Swap liquidity0 line shared by the inverse and original cursor. -/
def swapLiquidity0Line : List Ninst := [
  .reg .pop,
  .reg (.swap 1),
  .reg .pop,
  .reg (.swap 1),
  .reg .pop,
  .reg (.dup 1),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .reg (.dup 7),
  .reg .lt,
  .reg (.dup 0),
  .reg .iszero,
  .push [0x07, 0x9a] (by decide)]

theorem swapLiquidity0Line_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {ts r1 r0 len start toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (ts :: r1 :: r0 :: 0 :: 0 :: len :: start :: toWord :: a1 :: a0 :: rho :: S) M G) swapLiquidity0Line d) :
    ∃ G', d = St b
      ((Bytes.toB256 [0x07, 0x9a]) ::
       (B256.eqCheck (B256.ltCheck a0 ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& r0)) 0) ::
       (B256.ltCheck a0 ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& r0)) ::
       r1 ::
       r0 ::
       len ::
       start ::
       toWord ::
       a1 ::
       a0 ::
       rho :: S) M G' := by
  dsimp only [swapLiquidity0Line] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_lt step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  dsimp only [List.set] at state
  exact ⟨gas, state⟩

/-- Literal Swap liquidity1 line shared by the inverse and original cursor. -/
def swapLiquidity1Line : List Ninst := [
  .reg .pop,
  .reg (.dup 0),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .reg (.dup 6),
  .reg .lt]

theorem swapLiquidity1Line_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {flag r1 r0 len start toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (flag :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: S) M G) swapLiquidity1Line d) :
    ∃ G', d = St b
      ((B256.ltCheck a1 ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& r1)) ::
       r1 ::
       r0 ::
       len ::
       start ::
       toWord ::
       a1 ::
       a0 ::
       rho :: S) M G' := by
  dsimp only [swapLiquidity1Line] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_lt step
  cases line
  exact ⟨gas, state⟩

/-- Literal Swap tokenload line shared by the inverse and original cursor. -/
def swapTokenLoadLine : List Ninst := [
  .push [0x06] (by decide),
  .reg .sload,
  .push [0x07] (by decide),
  .reg .sload,
  .push [0x00] (by decide),
  .reg (.swap 1),
  .reg (.dup 2),
  .reg (.swap 1),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.swap 1),
  .reg (.dup 2),
  .reg .and,
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 1),
  .reg .and,
  .reg (.swap 0),
  .reg (.dup 9),
  .reg .and,
  .reg (.dup 2),
  .reg .eq,
  .reg (.dup 0),
  .reg .iszero,
  .reg (.swap 0),
  .push [0x08, 0x54] (by decide)]

theorem swapTokenLoadLine_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {r1 r0 len start toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (line : Line.Run sevm (St b (r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: S) M G) swapTokenLoadLine d) :
    ∃ G', d = St (afterSload sevm (afterSload sevm b (Bytes.toB256 [0x06])) (Bytes.toB256 [0x07]))
      ((Bytes.toB256 [0x08, 0x54]) ::
       (B256.eqCheck ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& (b.getStorVal sevm.currentTarget (Bytes.toB256 [0x06]))) (toWord &&& (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]))) ::
       (B256.eqCheck (B256.eqCheck ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& (b.getStorVal sevm.currentTarget (Bytes.toB256 [0x06]))) (toWord &&& (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]))) 0) ::
       ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& ((afterSload sevm b (Bytes.toB256 [0x06])).getStorVal sevm.currentTarget (Bytes.toB256 [0x07]))) ::
       ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& (b.getStorVal sevm.currentTarget (Bytes.toB256 [0x06]))) ::
       (Bytes.toB256 [0x00]) ::
       (Bytes.toB256 [0x00]) ::
       r1 ::
       r0 ::
       len ::
       start ::
       toWord ::
       a1 ::
       a0 ::
       rho :: S) M G' := by
  dsimp only [swapTokenLoadLine] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_sload fork step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_push step
  cases line
  dsimp only [List.set] at state
  exact ⟨gas, state⟩

/-- Literal Swap recipient1 line shared by the inverse and original cursor. -/
def swapRecipient1Line : List Ninst := [
  .reg .pop,
  .reg (.dup 0),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .reg (.dup 9),
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .reg .eq,
  .reg .iszero]

theorem swapRecipient1Line_inv {sevm : Sevm} {b d : Devm} {S : List B256}
    {flag t1 t0 z1 z0 r1 r0 len start toWord a1 a0 rho : B256} {M : Mem} {G : Nat}
    (line : Line.Run sevm (St b (flag :: t1 :: t0 :: z1 :: z0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: rho :: S) M G) swapRecipient1Line d) :
    ∃ G', d = St b
      ((B256.eqCheck (B256.eqCheck ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& toWord) ((Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]) &&& t1)) 0) ::
       t1 ::
       t0 ::
       z1 ::
       z0 ::
       r1 ::
       r0 ::
       len ::
       start ::
       toWord ::
       a1 ::
       a0 ::
       rho :: S) M G' := by
  dsimp only [swapRecipient1Line] at line
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas, state⟩ := ri_iszero step
  cases line
  exact ⟨gas, state⟩

/-- The internal reserve read after a nonzero output flag. -/
theorem swapReserves_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {flag len start toWord a1 a0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (flag :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G) t_0707_c2 seg) :
    flag ≠ 0 ∧ ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St (afterSload sevm b 8)
        (reserveTimestampRead (b.getStorVal sevm.currentTarget 8) ::
         reserve1Read (b.getStorVal sevm.currentTarget 8) ::
         reserve0Read (b.getStorVal sevm.currentTarget 8) ::
         0 :: 0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M gas) t_0767_c2 seg := by
  unfold t_0707_c2 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  -- end .branch t_070c_c2 t_075c_c2
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨nonzero, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_070c_c2.noOk = true))
  refine ⟨nonzero, ?_⟩
  unfold t_075c_c2 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapReserveSetupLine run
  obtain ⟨_, rfl⟩ := swapReserveSetupLine_inv line
  -- end .callNext 56 t_0767_c2
  cases run with
  | callHalt d hk pop callee =>
      rw [show cert.prog[56]? = some t_0d90_c56 from rfl] at hk
      cases hk
      have callee' := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨_, impossible⟩ := reserves_callee_inv fork (callee'.mono StepIn.toRun)
      cases impossible
  | callRet d hk pop callee body =>
      rw [show cert.prog[56]? = some t_0d90_c56 from rfl] at hk
      cases hk
      have callee' := (St.of_pop1 pop).2 ▸ callee
      obtain ⟨gas, returned⟩ := reserves_callee_inv fork (callee'.mono StepIn.toRun)
      cases returned
      exact ⟨gas, body⟩

/-- The lock test, lock store and output-amount guard: a successful swap body was entered
unlocked, in a non-static frame, with a nonzero output amount. -/
theorem swapLockOutput_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {len start toWord a1 a0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G) t_0683_c54 seg) :
    b.getStorVal sevm.currentTarget 12 = 1 ∧ sevm.isStatic = false ∧ (a0 ≠ 0 ∨ a1 ≠ 0) ∧
      ∃ gas, let locked := mintLockedWorld sevm b
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St (afterSload sevm locked 8)
          (reserveTimestampRead (locked.getStorVal sevm.currentTarget 8) ::
           reserve1Read (locked.getStorVal sevm.currentTarget 8) ::
           reserve0Read (locked.getStorVal sevm.currentTarget 8) ::
           0 :: 0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M gas) t_0767_c2 seg := by
  unfold t_0683_c54 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapLockGuardLine run
  obtain ⟨_, rfl⟩ := swapLockGuardLine_inv fork line
  -- end .branch t_068e_c54 t_06f4_c54
  rcases ric_branchP run with ⟨-, _, failed⟩ | ⟨accepted, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_068e_c54.noOk = true))
  have unlocked : b.getStorVal sevm.currentTarget 12 = 1 := by
    change B256.eqCheck (1 : B256) (b.getStorVal sevm.currentTarget 12) ≠ 0 at accepted
    by_cases eq : (1 : B256) = b.getStorVal sevm.currentTarget 12
    · exact eq.symm
    · simp only [B256.eqCheck, eq, ite_false] at accepted
      exact False.elim (accepted rfl)
  unfold t_06f4_c54 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapLockStoreLine run
  obtain ⟨nonstatic, _, rfl⟩ := swapLockStoreLine_inv fork line
  refine ⟨unlocked, nonstatic, ?_⟩
  rcases ric_branchToP (by intro bad; cases bad) (rfl : cert.prog[2]? = some t_0707_c2) run with
    ⟨zero, _, run⟩ | ⟨nonzero, _, run⟩
  · unfold t_0702_c54 at run
    obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapOutputFallbackLine run
    obtain ⟨_, rfl⟩ := swapOutputFallbackLine_inv line
    obtain ⟨flag, gas, body⟩ := swapReserves_inv fork run
    refine ⟨Or.inr ?_, gas, body⟩
    intro h
    rw [h] at flag
    exact flag (by decide)
  · obtain ⟨_, gas, body⟩ := swapReserves_inv fork run
    refine ⟨Or.inl ?_, gas, body⟩
    intro h
    rw [h] at nonzero
    exact nonzero (by decide)

/-- The liquidity guards, the two token loads and the recipient guard. -/
theorem swapGuards_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ts r1 r0 len start toWord a1 a0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (ts :: r1 :: r0 :: 0 :: 0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G)
      t_0767_c2 seg) :
    let m : B256 := 0xffffffffffffffffffffffffffffffffffffffff
    a0.toNat < (reserveMask112 &&& r0).toNat ∧ a1.toNat < (reserveMask112 &&& r1).toNat ∧
    (m &&& b.getStorVal sevm.currentTarget 6) ≠ (toWord &&& m) ∧
    (m &&& toWord) ≠ (m &&& (m &&& b.getStorVal sevm.currentTarget 7)) ∧
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St (afterSload sevm (afterSload sevm b 6) 7)
        ((m &&& b.getStorVal sevm.currentTarget 7) :: (m &&& b.getStorVal sevm.currentTarget 6) ::
          0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M gas) t_08bf_c4 seg := by
  intro m
  have ltOf : ∀ x y : B256, B256.eqCheck (B256.ltCheck x y) 0 = 0 → x.toNat < y.toNat := by
    intro x y h
    by_cases lt : x < y
    · exact B256.toNat_lt_toNat lt
    · simp only [B256.ltCheck, lt, ite_false] at h
      exact absurd h (by decide)
  have ltOf' : ∀ x y : B256, B256.ltCheck x y ≠ 0 → x.toNat < y.toNat := by
    intro x y h
    by_cases lt : x < y
    · exact B256.toNat_lt_toNat lt
    · simp only [B256.ltCheck, lt, ite_false] at h
      exact absurd rfl h
  have neOf : ∀ x y : B256, B256.eqCheck x y = 0 → x ≠ y := by
    intro x y h eq
    simp only [B256.eqCheck, eq, ite_true] at h
    exact absurd h (by decide)
  have s7 : (afterSload sevm b 6).getStorVal sevm.currentTarget 7 =
      b.getStorVal sevm.currentTarget 7 := by
    change ((afterSload sevm b 6).getStor sevm.currentTarget).get 7 =
      (b.getStor sevm.currentTarget).get 7
    rw [afterSload_getStor]
  unfold t_0767_c2 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapLiquidity0Line run
  obtain ⟨_, rfl⟩ := swapLiquidity0Line_inv line
  rcases ric_branchToP (by intro bad; cases bad) (rfl : cert.prog[3]? = some t_079a_c3) run with
    ⟨zero0, _, run⟩ | ⟨jump0, _, run⟩
  swap
  · unfold t_079a_c3 at run
    obtain ⟨_, run⟩ := ric_destP run
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨lt0, _, _⟩
    · exact False.elim (failed.false_of_noOk (by decide : t_079f_c3.noOk = true))
    · exact absurd (eq_zero_of_iszero_ne_zero jump0) lt0
  unfold t_0786_c2 at run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapLiquidity1Line run
  obtain ⟨_, rfl⟩ := swapLiquidity1Line_inv line
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨lt1, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_079f_c3.noOk = true))
  unfold t_07ef_c3 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapTokenLoadLine run
  obtain ⟨_, rfl⟩ := swapTokenLoadLine_inv fork line
  rcases ric_branchToP (by intro bad; cases bad) (rfl : cert.prog[4]? = some t_0854_c4) run with
    ⟨eq0, _, run⟩ | ⟨jump1, _, run⟩
  swap
  · unfold t_0854_c4 at run
    obtain ⟨_, run⟩ := ric_destP run
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨ne0, _, _⟩
    · exact False.elim (failed.false_of_noOk (by decide : t_0859_c4.noOk = true))
    · exact absurd (eq_zero_of_iszero_ne_zero ne0) jump1
  unfold t_0823_c3 at run
  obtain ⟨d, line, run⟩ := SFunc.RunCutP.split_nexts StepIn.toRun swapRecipient1Line run
  obtain ⟨_, rfl⟩ := swapRecipient1Line_inv line
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨ne1, _, run⟩
  · exact False.elim (failed.false_of_noOk (by decide : t_0859_c4.noOk = true))
  simp only [show Bytes.toB256 [6] = (6 : B256) from rfl, show Bytes.toB256 [7] = (7 : B256) from rfl,
    show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
      255, 255, 255, 255] = m from rfl,
    show Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] =
      reserveMask112 from rfl] at run ne1 eq0 zero0 lt1
  rw [s7] at run ne1
  exact ⟨ltOf _ _ zero0, ltOf' _ _ lt1, neOf _ _ eq0,
    fun eq => ne1 (by rw [eq]; simp only [B256.eqCheck, ite_true]; decide), _, run⟩

/-- The raw world at the optimistic-transfer branch: lock store, reserve read, token loads. -/
def swapPrefixWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6) 7

/-- The body's locals at the optimistic-transfer branch, as the source state names them:
cached token1/token0 words, the two zero balance slots, the cached reserves, and the decoded
arguments. Every later front segment keeps this stack. -/
def swapLocalsStack (sevm : Sevm) (st : State) : List B256 :=
  st.token1.toB256 :: st.token0.toB256 :: 0 :: 0 :: Nat.toB256 st.reserve1.val ::
    Nat.toB256 st.reserve0.val :: swapBodyStack sevm

/-- The actual swap body prefix against the finite entry storage: the lock was open, the frame
is non-static, every source guard of `startTyped` held on the decoded arguments and the cached
state, and the run continues at the transfer branch with the source-named locals. -/
theorem swapBody_prefix_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv} {sevm : Sevm}
    {b : Devm} {M : Mem} {G : Nat} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (swapBodyStack sevm) M G) t_0683_c54 seg) :
    st.unlocked = 1 ∧ sevm.isStatic = false ∧
    (swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0) ∧
    (swapAmount0Out sevm).toNat < st.reserve0.val ∧ (swapAmount1Out sevm).toNat < st.reserve1.val ∧
    swapRecipient sevm ≠ st.token0 ∧ swapRecipient sevm ≠ st.token1 ∧
    ∃ gas, SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St (swapPrefixWorld sevm b) (swapLocalsStack sevm st) M gas) t_08bf_c4 seg := by
  obtain ⟨unlockedRaw, nonstatic, output, _, run⟩ := swapLockOutput_inv fork run
  obtain ⟨lt0, lt1, ne0, ne1, gas, run⟩ := swapGuards_inv fork run
  have lockedRep := rep.mint_locked_world (sevm := sevm) (b := b)
  rcases lockedRep.fixed with ⟨_, _, _, token0Fixed, token1Fixed, cache0, cache1, _, _, _, _, _⟩
  have unlocked : st.unlocked = 1 := by
    rcases rep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, _, fixed⟩
    exact fixed.symm.trans unlockedRaw
  let m : B256 := 0xffffffffffffffffffffffffffffffffffffffff
  have maskWord : ∀ x : B256, m &&& x = x.toAdr.toB256 := ff20_and_word
  have maskIdem : ∀ x : B256, m &&& (x &&& m) = x.toAdr.toB256 := by
    intro x
    rw [B256.and_comm, B256.and_idem_right, B256.and_comm, maskWord]
  have resIdem : ∀ w : B256, reserveMask112 &&& reserve0Read w = reserve0Read w := by
    intro w
    rw [reserve0Read, B256.and_comm, B256.and_idem_right]
  have resIdem1 : ∀ w : B256, reserveMask112 &&& reserve1Read w = reserve1Read w := by
    intro w
    rw [reserve1Read, B256.and_comm, B256.and_idem_right]
  let locked := mintLockedWorld sevm b
  have slot (k : B256) : (afterSload sevm locked 8).getStorVal sevm.currentTarget k =
      (locked.getStor sevm.currentTarget).get k := by
    change ((afterSload sevm locked 8).getStor sevm.currentTarget).get k = _
    rw [afterSload_getStor]
  change reserve0Read ((locked.getStor sevm.currentTarget).get 8) = _ at cache0
  change reserve1Read ((locked.getStor sevm.currentTarget).get 8) = _ at cache1
  change reserve0Read (locked.getStorVal sevm.currentTarget 8) = _ at cache0
  change reserve1Read (locked.getStorVal sevm.currentTarget 8) = _ at cache1
  rw [resIdem, cache0, B256.toNat_toB256_of_lt
    (lt_trans st.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))] at lt0
  rw [resIdem1, cache1, B256.toNat_toB256_of_lt
    (lt_trans st.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))] at lt1
  have word0 : m &&& (afterSload sevm locked 8).getStorVal sevm.currentTarget 6 = st.token0.toB256 := by
    rw [maskWord, slot, token0Fixed]
  have word1 : m &&& (afterSload sevm locked 8).getStorVal sevm.currentTarget 7 = st.token1.toB256 := by
    rw [maskWord, slot, token1Fixed]
  have recipientWord : swapRecipientWord sevm &&& m = (swapRecipient sevm).toB256 := by
    rw [swapRecipientWord, B256.and_idem_right, B256.and_comm, maskWord]
    rfl
  have recipientWord' : m &&& swapRecipientWord sevm = (swapRecipient sevm).toB256 := by
    rw [B256.and_comm, recipientWord]
  have word1' : m &&& (m &&& (afterSload sevm locked 8).getStorVal sevm.currentTarget 7) =
      st.token1.toB256 := by
    rw [word1, maskWord, toAdr_toB256]
  rw [word0, recipientWord] at ne0
  rw [recipientWord', word1'] at ne1
  rw [word0, word1] at run
  refine ⟨unlocked, nonstatic, output, lt0, lt1, fun eq => ne0 (by rw [eq]),
    fun eq => ne1 (by rw [eq]), gas, ?_⟩
  rw [cache0, cache1] at run
  exact run

end Blanc.Lift.UniswapV2Pair
