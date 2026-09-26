import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment B1: the guards and the two `to_little_endian_64` calls, inverted

The converse of `body_guards`: a successful run of the body's entry passes its six guards, which
fixes the three lengths and gives the three value conditions, and reaches the return tag `0x0575`
in the state `body_guards` describes (gas aside).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeGuards
/-- **Inversion of segment 1 (`t_0304_c7 → t_0575_c7`).**

Proof sketch.  `cases` along the walk `body_guards` takes.  Each guard's failing arm is an
`Error(string)` block (`MLOAD`, `MSTORE`s, `CODECOPY`, `REVERT`) with no successful terminal, so
`EQ` of the lengths is `1` (`B256.eqCheck`), `CALLVALUE < 1 ether` is `0`, `CALLVALUE mod 1 gwei`
is `0` and `amount > 2^64 - 1` is `0`; convert with `B256.toNat_div`/`toNat_mod` and
`B256.lt_iff_toNat_lt_toNat`.  The two `callNext 25` nodes are `.callRet` (entry 25 has no
successful halting leaf); invert `to_little_endian_64` once as a lemma about entry 25 for any
caller (the converse of `to_little_endian_64_run`: from a run of `t_14ba_c25` returning, the
returned state is `pB :: rest` over `leImg`; its eight `MSTORE8` bounds checks have `INVALID`
failing arms).  The `SLOAD` is `Ninst.Run`'s `afterSload` successor (determinism of the step:
compare with `Ninst.runCompiled_sload_selected`). -/
theorem safe_guards {sevm : Sevm} {b : Devm} {sel rt sP wP pP pkL wcL sgL : B256} {G : Nat}
    {o : Outcome}
    (hcd : sevm.data.length < 2 ^ 256) (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St b [rt, sgL, sP, wcL, wP, pkL, pP, 0x01b8, sel] mem0 G)
      t_0304_c7 o) :
    pkL = 48 ∧ wcL = 32 ∧ sgL = 96 ∧ 10 ^ 18 ≤ sevm.value.toNat ∧
      sevm.value.toNat % 10 ^ 9 = 0 ∧ sevm.value.toNat / 10 ^ 9 < 2 ^ 64 ∧
      ∃ b' M' G', Keep (afterSload sevm b solCountSlot) b' ∧
        BodyMem M' 256 0x100
          [(0x80, (8 : B256).toBytes), (0xa0, BeaconDeposit.le64 (gweiAmount sevm).toNat),
            (0xc0, (8 : B256).toBytes),
            (0xe0, BeaconDeposit.le64 (b.getStorVal sevm.currentTarget solCountSlot).toNat)] ∧
        SFunc.Run prog sevm
          (St b' [0xc0, 96, sP, 0x80, 32, wP, 48, pP, BeaconDeposit.depositEventTopic, 0x80,
            gweiAmount sevm, rt, 96, sP, 32, wP, 48, pP, 0x01b8, sel] M' G') t_0575_c7 o := by
  sorry

end Blanc.Lift.BeaconDeposit
