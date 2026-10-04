import Blanc.Lift.UniswapV2Pair.Creation.Cert
import Blanc.Lift.UniswapV2Pair.Cert
import Blanc.Lift.Create2Deploy

/-!
# Closed kernel facts about the Pair creation bytes

Every statement here is a closed computation on literal bytes, decided by the kernel
(`decide +kernel`, kernel evaluation only, no hash premise).  They live apart from the walks so that
no language-server worker elaborates them while a walk is edited.

* the creation code's trailing 82 bytes are the EIP-712 domain type string, and the runtime window
  `[0x105, 0x105 + 11293)` is exactly the certified runtime `Blanc.Lift.UniswapV2Pair.code`;
* the type hash and the name/version hashes the constructor pushes are the Keccak digests of the
  type string, `"Uniswap V2"` and `"1"`;
* the exhibit pair (USDC/WETH): its salt is `keccak(token0 ‖ token1)`, its init-code hash is the
  digest of all 11,636 creation bytes, and its address is `create2NewAddress factory salt code`;
  a salt or digest off by one bit gives a different address (the statement controls).
-/

namespace Blanc.Lift.UniswapV2Pair.Creation

open Jaune Blanc.Lift

/-- `EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)`. -/
def typeString : Bytes := [
  0x45, 0x49, 0x50, 0x37, 0x31, 0x32, 0x44, 0x6f, 0x6d, 0x61, 0x69, 0x6e, 0x28, 0x73, 0x74, 0x72,
  0x69, 0x6e, 0x67, 0x20, 0x6e, 0x61, 0x6d, 0x65, 0x2c, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67, 0x20,
  0x76, 0x65, 0x72, 0x73, 0x69, 0x6f, 0x6e, 0x2c, 0x75, 0x69, 0x6e, 0x74, 0x32, 0x35, 0x36, 0x20,
  0x63, 0x68, 0x61, 0x69, 0x6e, 0x49, 0x64, 0x2c, 0x61, 0x64, 0x64, 0x72, 0x65, 0x73, 0x73, 0x20,
  0x76, 0x65, 0x72, 0x69, 0x66, 0x79, 0x69, 0x6e, 0x67, 0x43, 0x6f, 0x6e, 0x74, 0x72, 0x61, 0x63,
  0x74, 0x29]

/-- `"Uniswap V2"`, the token name. -/
def nameBytes : Bytes := [0x55, 0x6e, 0x69, 0x73, 0x77, 0x61, 0x70, 0x20, 0x56, 0x32]

/-- `"1"`, the domain version. -/
def versionBytes : Bytes := [0x31]

def typeHash : B256 := 0x8b73c3c69bb8fe3d512ecc4cf759cc79239f7b179b0ffacaa9a75d522b39400f
def nameHash : B256 := 0xbfcc8ef98ffbf7b6c3fec7bf5185b566b9863e35a9d83acd49ad6824b5969738
def versionHash : B256 := 0xc89efdaa54c0f20c7adf612882df0950f5a951637e0307cdcb4c672f298b8bc6

theorem typeHash_eq : Bytes.keccak typeString = typeHash := by decide +kernel
theorem nameHash_eq : Bytes.keccak nameBytes = nameHash := by decide +kernel
theorem versionHash_eq : Bytes.keccak versionBytes = versionHash := by decide +kernel

theorem code_toList : code.toList = codeChunk0 ++ codeChunk1 ++ codeChunk2 := by
  rw [ByteArray.toList_eq_toList_data]
  rfl

theorem code_toList_length : code.toList.length = 11636 := by
  rw [code_toList]
  decide +kernel

/-- The constructor's `CODECOPY` of the type string reads the code's last 82 bytes. -/
theorem typeWindow_eq : code.sliceD 0x2d22 0x52 (Linst.toUInt8 .stop) = typeString := by
  rw [ByteArray.sliceD_eq, code_toList]
  decide +kernel

/-- The window the constructor returns. -/
def runtimeWindow : Bytes := code.sliceD 0x105 0x2c1d (Linst.toUInt8 .stop)

/-- The returned window is exactly the certified runtime. -/
theorem runtimeWindow_eq : runtimeWindow = Blanc.Lift.UniswapV2Pair.code.toList := by
  rw [runtimeWindow, ByteArray.sliceD_eq, code_toList, ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

/-- The certified runtime does not start with `0xEF` (the CREATE code-prefix rule). -/
theorem runtime_head : Blanc.Lift.UniswapV2Pair.code.toList.head? ≠ some 0xEF := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-! ## The exhibit pair -/

/-- The Uniswap V2 factory. -/
def factory : Adr := 0x5c69bee701ef814a2b6a3edd4b1652cb9cc5aa6f
/-- USDC, the exhibit pair's `token0`. -/
def token0 : Adr := 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48
/-- WETH, the exhibit pair's `token1`. -/
def token1 : Adr := 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2
/-- The exhibit USDC/WETH pair. -/
def pairAddress : Adr := 0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc

/-- The factory's salt, `keccak256(abi.encodePacked(token0, token1))`. -/
def salt : B256 := Bytes.keccak (token0.toBytes ++ token1.toBytes)

def saltWord : B256 := 0x85053f65cd1ece2bb37b70c13d66eadebf2779df5ddd68cf12f3ccfdc6bfe760
def initHash : B256 := 0x96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f

theorem salt_eq : salt = saltWord := by decide +kernel

/-- The init-code hash is the digest of all 11,636 creation bytes. -/
theorem initHash_eq : Bytes.keccak code.toList = initHash := by
  rw [code_toList]
  decide +kernel

theorem pairAddress_ofHash : create2AddressOfHash factory saltWord initHash = pairAddress := by
  decide +kernel

/-- **The exhibit pair's address** is the CREATE2 address of the actual creation code from the
factory with salt `keccak(token0 ‖ token1)`. -/
theorem pairAddress_eq : pairAddress = create2NewAddress factory salt code.toList := by
  rw [create2NewAddress_eq_ofHash, initHash_eq, salt_eq, pairAddress_ofHash]

/-- Statement control: a salt one bit off gives another address. -/
theorem pairAddress_wrong_salt :
    create2AddressOfHash factory (saltWord ^^^ 1) initHash ≠ pairAddress := by
  decide +kernel

/-- Statement control: an init-code digest one bit off gives another address. -/
theorem pairAddress_wrong_initHash :
    create2AddressOfHash factory saltWord (initHash ^^^ 1) ≠ pairAddress := by
  decide +kernel

end Blanc.Lift.UniswapV2Pair.Creation
