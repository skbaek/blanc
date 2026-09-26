import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Safety segment W: the `deposit` wrapper and ABI decoder, inverted

A successful run of the `deposit` wrapper (entry 32) passes every decoder guard — the calldata is
`DepositDecodable` — calls the body (entry 7) from the frozen argument stack over `mem0`, and
halts by the `STOP` at the return tag `0x01b8`, whose post state has the body's storage and logs.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

-- SEGMENT: safeDecoder
/-- **Decoder inversion (`t_00a4_c32`, about 200 nodes).**

Proof sketch.  Walk the wrapper's straight lines by `cases` (as `safe_dispatch`); each of the
decoder's `JUMPI` guards (head size `CDS - 4 ≥ 0x80`, per tail the four comparisons of
`TailDecodable`) has its failing arm end in `PUSH 0 DUP REVERT`, which has no successful
`Linst.Run`, so each comparison word is `0`/nonzero as `DepositDecodable` states (read the
words through `B256.ltCheck`/`gtCheck` and `toNat`; `hcd` keeps `CALLDATASIZE` exact).  The
`callNext 7 t_01b8_c32` node is `.callRet` (the body only returns: `.callHalt` would need the
body to halt successfully, and the body has no successful halting leaf — or keep both cases and
note `callHalt` gives `.halted` directly, which the statement also covers by taking the body's
result); the pushed words are `depositArgStack sevm [sel]` (`DepositArgs.lean`).  `t_01b8_c32`
is `JUMPDEST; STOP`: `Burn.world` and `Linst.world_of_ok` (`Quiet.lean`). -/
theorem safe_decoder {sevm : Sevm} {b post : Devm} {sel : B256} {G : Nat}
    (hcd : sevm.data.length < 2 ^ 256)
    (run : SFunc.Run prog sevm (St b [sel] mem0 G) t_00a4_c32 (.halted post)) :
    DepositDecodable sevm ∧ ∃ G' d,
      SFunc.Run prog sevm (St b (depositArgStack sevm [sel]) mem0 G') t_0304_c7 (.returned d) ∧
      (∀ a, Devm.getStor post a = Devm.getStor d a) ∧ post.logs = d.logs := by
  sorry

end Blanc.Lift.BeaconDeposit
