import Blanc.Lift.BuilderRequest.Deposit.Latch
import Blanc.Lift.BuilderRequest.Exit.Latch

/-!
# The builder contracts' system calls move no balance, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`. A statement of one call
each: no history. The storage writes are all the call does to the state (`sysState`, `latchState`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune

/-- **Neither builder's system call changes any account's balance**, from any storage, with either
calldata form. Each conjunct takes its contract's canonical code as installed. `hlen` says `CALLDATASIZE`
reads the length faithfully. -/
theorem system_calls_keep_balances {benv : Benv} {data : Bytes} (hfork : benv.stat.fork = .amsterdam)
    (hlen : data.length < 2 ^ 256) :
    (benv.state.getCode Deposit.Creation.address = Deposit.code →
      KeepsBalances benv Deposit.Creation.address data) ∧
    (benv.state.getCode Exit.Creation.address = Exit.code →
      KeepsBalances benv Exit.Creation.address data) :=
  ⟨fun installed => keepsBalances Deposit.sysCall Deposit.sysWords rfl rfl hfork installed hlen,
    fun installed => keepsBalances Exit.sysCall Exit.sysWords rfl rfl hfork installed hlen⟩

end Blanc.Lift.BuilderRequest
