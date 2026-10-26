import Blanc.Lift.Usdc.ProxyCreation.Cert
import Blanc.Lift.Usdc.Constants

/-!
# Checked constants of the original proxy constructor

Only finite input-window and fixed-label identities live here. The execution
proof uses the registered input and the constructor's actual stored words.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune

/-- The V1 implementation word encoded in the original constructor input. -/
def initialImplementation : B256 :=
  0x0882477e7895bdc5cea7cb1552ed914ab157fe56

def implementationLabelLeft : B256 :=
  0x6f72672e7a657070656c696e6f732e70726f78792e696d706c656d656e746174

def implementationLabelRight : B256 :=
  0x696f6e0000000000000000000000000000000000000000000000000000000000

def adminLabelWord : B256 :=
  0x6f72672e7a657070656c696e6f732e70726f78792e61646d696e000000000000

/-- The trailing ABI word of the registered original creation input. -/
theorem argument_window :
    code.toList.sliceD 2857 32 0 = initialImplementation.toBytes := by
  rw [ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- The exact bytes written and selected by the implementation-label hash. -/
theorem implementationLabel_bytes :
    (implementationLabelLeft.toBytes ++ implementationLabelRight.toBytes).sliceD 0 35 0 =
      String.toBytes "org.zeppelinos.proxy.implementation" := by
  apply eq_of_beq
  decide +kernel

/-- The exact bytes written and selected by the admin-label hash. -/
theorem adminLabel_bytes :
    adminLabelWord.toBytes.sliceD 0 26 0 =
      String.toBytes "org.zeppelinos.proxy.admin" := by
  apply eq_of_beq
  decide +kernel

theorem implementationLabel_hash :
    (String.toBytes "org.zeppelinos.proxy.implementation").keccak = implSlot := by
  apply eq_of_beq
  decide +kernel

theorem adminLabel_hash :
    (String.toBytes "org.zeppelinos.proxy.admin").keccak = adminSlot := by
  apply eq_of_beq
  decide +kernel

end Blanc.Lift.Usdc.ProxyCreation
