import Blanc.Lift.VyperNonreentrantDeployed.Token20.Cert
import Blanc.Lift.Exact
import Blanc.Lift.MapSlot
import Blanc.ExecutionReachable

/-!
# The synthetic minimal ERC-20 `T` of the reachable V± witnesses: certificate and layout

`code` (`Cert.lean`, generated from `scripts/lift/inputs/vyper-token20-runtime.hex`) is a
**synthetic**, hand-assembled 299-byte token, not a mainnet contract.  It dispatches on the
first four calldata bytes (`CALLDATALOAD(0) >> 224`):

* `transfer(address,uint256)` `0xa9059cbb`, `transferFrom(address,address,uint256)`
  `0x23b872dd`, `balanceOf(address)` `0x70a08231`, `approve(address,uint256)` `0x095ea7b3`;
  any other selector reverts with empty data.
* `balanceOf[a]` is at slot `balSlot a = a` (the address word); `allowance[o][s]` at
  `allowSlot o s = keccak256(pad32(o) ‖ pad32(s))` (`mapSlot`).
* The bytes check the ordinary conditions: as a behaviour of the bytes, **not proved by any
  theorem** (only the success runs are proved, in `Run.lean`), `transferFrom` reverts when
  `value > allowance` and a move reverts when `value > balanceOf[from]` or when the credit
  wraps.  `transferFrom` always decrements the allowance: there is no infinite-allowance case,
  also when `from = caller`.  Success returns the 32-byte word `1`.  Address arguments are
  masked to 160 bits.
* No events, no payable guard, no calldata-length check.

This module holds the kernel acceptance of the certificate (`cert_check`, `cert_jumpsOk`), the
storage layout, and the fact that no reachable instruction can spawn a frame (`spawnFreeReach`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc.Lift

theorem cert_check : Cert.check code cert = true := by decide +kernel

theorem cert_jumpsOk : Cert.jumpsOk code cert = true := by decide +kernel

/-- The lifted program. -/
abbrev prog : List SFunc := Cert.prog cert

/-- `balanceOf[a]` lives at the address word. -/
def balSlot (a : Adr) : B256 := a.toB256

/-- `allowance[owner][spender]` lives at `keccak256(pad32(owner) ‖ pad32(spender))`. -/
def allowSlot (owner spender : Adr) : B256 := mapSlot owner.toB256 spender.toB256

/-- No `CALL`- or `CREATE`-family instruction starts at a position an execution reaches. -/
theorem spawnFreeReach : SpawnFreeReach code := spawnFreeReach_of_check (by decide +kernel)

end Blanc.Lift.VyperNonreentrantDeployed.Token20
