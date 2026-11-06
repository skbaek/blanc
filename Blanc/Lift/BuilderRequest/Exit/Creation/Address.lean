import Blanc.Lift.BuilderRequest.Exit.Creation.Input
import Blanc.Lift.Create2Factory.Walk

/-!
# The builder exit contract's address, computed from its init code

The address is the CREATE2 address of the factory, the recorded salt and the keccak-256 of the
recorded init code, each computed by the kernel.
-/

namespace Blanc.Lift.BuilderRequest.Exit.Creation

open Jaune Blanc.Lift Blanc.Lift.Create2Factory

/-- The salt recorded in the deployment transaction. -/
def salt : B256 := 0x89abb1878437213f971f849327423ed1d9c5cdb03970cd8f0000318b3ff10119

/-- The address the mainnet contract occupies. -/
def address : Adr := 0x000064d678505ad48f8ccb093bc65613800e8282

/-- The recorded init code as a byte list. -/
def initBytes : Bytes := constructorPrefix ++ Blanc.Lift.BuilderRequest.Exit.code.toList

theorem initBytes_length : initBytes.length = 503 := by
  decide +kernel

/-- The keccak-256 of the init code, computed by the kernel. -/
theorem initBytes_keccak :
    Bytes.keccak initBytes = 0x7a6f1735761067dc2d2aad939590e0d78e2588abf983412ab6f20896a21125f1 := by
  decide +kernel

/-- The factory, the salt and the init code's digest compute the contract's address. -/
theorem address_eq : create2NewAddress factoryAddress salt initBytes = address := by
  rw [create2NewAddress_eq_ofHash, initBytes_keccak]
  decide +kernel

theorem address_ne_factory : address ≠ factoryAddress := by
  decide +kernel

theorem address_toB256_ne_zero : address.toB256 ≠ 0 := by
  decide +kernel

theorem calldata_length_word : (salt.toBytes ++ initBytes).length.toB256 + negWord = 503 := by
  decide +kernel

end Blanc.Lift.BuilderRequest.Exit.Creation
