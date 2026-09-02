import Blanc.ProxyPairSlots

/-!
# The selector-free forwarding proxy artifact

This module owns the proxy program and its compiled artifact.  The
implementation slot is carried as the published literal so compilation does
not re-elaborate the Keccak expression; `implementationSlotLit_eq_slot` is the
single bridge back to the derived slot declaration.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## ERC-1967 implementation slot literal -/

def implementationSlotLit : B256 :=
  0x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc

theorem implementationSlotLit_eq_slot :
    implementationSlotLit = implementationSlot := by
  unfold implementationSlotLit
  rw [implementationSlot_val]

/-! ## Selector-free fallback -/

/-- Copy the complete delegated returndata, then return on a nonzero child
status and revert on zero.  The forwarding program and the full Lido runtime
share this exact tail. -/
def proxyReturnTail : Func :=
  pushB256 0 ::: returndatasize ::: pushB256 0 ::: pushB256 0 :::
  returndatacopy ::: returndatasize ::: swap 1 :::
  Func.branch
    (Func.last .revert)
    (Func.last .return_)

def proxyFallback : Func :=
  -- Copy the whole calldata to memory[0 .. cds).
  calldatasize ::: pushB256 0 ::: pushB256 0 ::: calldatacopy :::
  -- Push the six DELEGATECALL operands deepest first.
  pushB256 0 :::
  pushB256 0 :::
  calldatasize :::
  pushB256 0 :::
  pushB256 implementationSlotLit ::: sload :::
  gas :::
  delegatecall :::
  -- Retain one zero beneath the status word while copying returndata.  A
  -- second RETURNDATASIZE is cheaper than DUP and leaves the shared
  -- RETURN/REVERT offset outside the two branch arms.
  proxyReturnTail

def proxyProg : Prog := ⟨proxyFallback, []⟩

def proxyBytes : Bytes := (Prog.compile proxyProg).getD []

def proxyCode : ByteArray := ByteArray.mk proxyBytes.toArray

theorem proxyProg_compiles : proxyProg.compiles = true := by
  decide

theorem proxyProg_compile : Prog.compile proxyProg = some proxyBytes :=
  Prog.compile_eq_some_getD_of_compiles _ proxyProg_compiles

theorem proxyBytes_length : proxyBytes.length = 59 := by
  decide +kernel

theorem proxyCode_notDelegation : getDelegatedCodeAddress proxyCode = none := by
  decide +kernel

end Blanc.ProxyPair
