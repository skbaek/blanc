import Blanc.Lift.BuilderRequest.Deposit.Creation.Input
import Blanc.Lift.Create2Factory.Walk

/-!
# The builder deposit contract's address, computed from its init code

The address is the CREATE2 address of the factory, the recorded salt and the keccak-256 of the
recorded init code, each computed by the kernel.
-/

namespace Blanc.Lift.BuilderRequest.Deposit.Creation

open Jaune Blanc.Lift Blanc.Lift.Create2Factory

/-- The salt recorded in the deployment transaction. -/
def salt : B256 := 0x1f4f2c41c28e816e259b621c58b94b37309c8dec42c8f6e400001a46c9d96bf7

/-- The address the mainnet contract occupies. -/
def address : Adr := 0x0000bff46984e3725691fa540a8c7589300d8282

/-- The recorded init code as a byte list. -/
def initBytes : Bytes := constructorPrefix ++ Blanc.Lift.BuilderRequest.Deposit.code.toList

theorem initBytes_length : initBytes.length = 638 := by
  decide +kernel

/-- The keccak-256 of the init code, computed by the kernel. -/
theorem initBytes_keccak :
    Bytes.keccak initBytes = 0x28fea4efa57c16b7f3b97372eda9c84ac0941263c121571027957d783017f9fd := by
  decide +kernel

/-- The factory, the salt and the init code's digest compute the contract's address. -/
theorem address_eq : create2NewAddress factoryAddress salt initBytes = address := by
  rw [create2NewAddress_eq_ofHash, initBytes_keccak]
  decide +kernel

theorem address_ne_factory : address ≠ factoryAddress := by
  decide +kernel

theorem address_toB256_ne_zero : address.toB256 ≠ 0 := by
  decide +kernel

theorem calldata_length_word : (salt.toBytes ++ initBytes).length.toB256 + negWord = 638 := by
  decide +kernel

end Blanc.Lift.BuilderRequest.Deposit.Creation
