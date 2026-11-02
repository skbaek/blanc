import Blanc.Lift.Weth9.Creation.Block.Header
import Blanc.Lift.Weth9.Creation.Block.ReceiptCert0
import Blanc.Lift.Weth9.Creation.Block.ReceiptCert1
import Blanc.Lift.Weth9.Creation.Block.ReceiptCert2

/-! Generated only by scripts/weth9-creation-block-generate.py.
The receipt trie root of block 4,719,568, through the certified twin. -/

namespace Blanc.Lift.Weth9.Creation.Block

open Jaune Blanc.TrieKernel

theorem receiptCert₀_valid : receiptCert₀.Forall (fun p => Bytes.keccak p.1 = p.2) :=
  ⟨rk0, rk1, rk2, rk3, rk4, rk5, rk6, rk7, rk8, rk9, rk10, rk11,
   rk12, rk13, rk14, rk15, rk16, rk17, rk18, rk19, rk20, rk21, rk22, rk23,
   rk24, rk25, rk26, rk27, rk28, rk29, rk30, rk31, rk32, rk33, rk34, rk35,
   rk36, rk37, rk38, rk39, rk40, rk41, rk42, rk43, rk44, rk45, rk46, rk47,
   rk48, rk49, rk50, rk51, rk52, rk53, rk54, rk55, rk56, rk57, rk58, rk59,
   rk60, rk61, rk62, rk63, rk64, rk65, rk66, rk67, rk68, rk69, rk70, rk71,
   rk72, rk73, rk74, rk75, rk76, rk77, rk78, rk79, rk80, rk81, rk82, rk83,
   rk84, rk85, rk86, rk87, rk88, rk89, rk90, rk91, rk92, rk93, rk94, rk95,
   rk96, rk97, rk98, rk99, rk100, rk101, rk102, rk103, rk104, rk105, rk106, rk107,
   rk108, rk109, rk110, rk111, rk112, rk113, rk114, rk115, rk116, rk117, rk118, rk119,
   rk120, rk121, rk122, rk123, rk124, rk125, rk126, rk127, rk128, rk129, rk130, rk131,
   rk132, rk133, rk134, rk135, rk136, rk137, rk138, rk139, rk140, rk141, rk142, rk143,
   rk144, rk145, rk146, rk147, rk148⟩

/-- Jaune's `trie` over the entries is the header's root, checked in the kernel. -/
theorem receiptTrie_root : trie receiptNTB₀ = receiptRoot₀ := by
  rw [trie_eq_cached receiptCert₀ receiptCert₀_valid]; decide +kernel

end Blanc.Lift.Weth9.Creation.Block
