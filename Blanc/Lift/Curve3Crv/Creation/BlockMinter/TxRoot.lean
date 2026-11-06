import Blanc.Lift.Curve3Crv.Creation.BlockMinter.Header
import Blanc.Lift.Curve3Crv.Creation.BlockMinter.TxCert0
import Blanc.Lift.Curve3Crv.Creation.BlockMinter.TxCert1

/-! Generated only by scripts/curve-3pool-block-generate.py.
The tx trie root of block 10,809,482, through the certified twin. -/

namespace Blanc.Lift.Curve3Crv.Creation.BlockMinter

open Jaune Blanc.TrieKernel

theorem txCert₀_valid : txCert₀.Forall (fun p => Bytes.keccak p.1 = p.2) :=
  ⟨tk0, tk1, tk2, tk3, tk4, tk5, tk6, tk7, tk8, tk9, tk10, tk11,
   tk12, tk13, tk14, tk15, tk16, tk17, tk18, tk19, tk20, tk21, tk22, tk23,
   tk24, tk25, tk26, tk27, tk28, tk29, tk30, tk31, tk32, tk33, tk34, tk35,
   tk36, tk37, tk38, tk39, tk40, tk41, tk42, tk43, tk44, tk45, tk46, tk47,
   tk48, tk49, tk50, tk51, tk52, tk53, tk54, tk55, tk56, tk57, tk58, tk59,
   tk60, tk61, tk62, tk63, tk64, tk65, tk66, tk67, tk68, tk69, tk70, tk71,
   tk72, tk73, tk74, tk75, tk76, tk77, tk78, tk79, tk80, tk81, tk82, tk83,
   tk84, tk85, tk86, tk87, tk88, tk89, tk90, tk91, tk92, tk93, tk94, tk95,
   tk96, tk97, tk98, tk99, tk100, tk101, tk102, tk103, tk104, tk105, tk106, tk107,
   tk108, tk109, tk110, tk111, tk112, tk113, tk114, tk115, tk116, tk117, tk118, tk119,
   tk120, tk121, tk122, tk123, tk124, tk125, tk126, tk127, tk128, tk129, tk130, tk131,
   tk132, tk133, tk134, tk135, tk136, tk137, tk138, tk139, tk140, tk141, tk142, tk143,
   tk144, tk145, tk146, tk147, tk148, tk149, tk150, tk151, tk152, tk153, tk154, tk155,
   tk156, tk157, tk158, tk159, tk160, tk161, tk162, tk163, tk164, tk165, tk166, tk167,
   tk168, tk169, tk170⟩

/-- Jaune's `trie` over the entries is the header's root, checked in the kernel. -/
theorem txTrie_root : trie txNTB₀ = transactionRoot₀ := by
  rw [trie_eq_cached txCert₀ txCert₀_valid]; decide +kernel

end Blanc.Lift.Curve3Crv.Creation.BlockMinter
