import Blanc.Lift.Usdc.Proxy.Cert

/-! Concrete C1 control: the proxy certificate with its DELEGATECALL claimed as a CALL is rejected.

`callMutant` is the generated node `t_0682_c23` (the `Proxy._delegate` block entered at the
JUMPDEST `0x682`) with its `.exec .delegatecall` at byte `1680` (`0x690`, opcode `0xf4`) replaced
by `.exec .call`; `mutant` is `cert` with entry 23's node replaced by it and nothing else
changed.  `Proxy.cert_check` accepts `cert`; the kernel rejects `mutant`, since the code byte is
`0xf4`, not CALL's `0xf1` (and CALL pops seven words, DELEGATECALL six).  Narrow-build-only. -/

namespace Blanc.Lift.Usdc.Proxy

open Jaune

/-- `t_0682_c23` with the DELEGATECALL node at byte `1680` replaced by `.exec .call`. -/
def callMutant : SFunc := (.dest (.next (.reg .calldatasize) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .calldatacopy) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .calldatasize) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 4)) (.next (.reg .gas) (.next (.exec .call) (.next (.reg .returndatasize) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .returndatacopy) (.next (.reg (.dup 0)) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.push [0x06, 0xa3] (by decide)) (.branch t_069f_c23 t_06a3_c23))))))))))))))))))))))

/-- The proxy certificate with entry 23 (`0x682`) running `callMutant`. -/
def mutant : Cert :=
  cert.set 23 (⟨0x682, [.unk, (.const (Nat.toB256 0x211)), (.const (Nat.toB256 0x75)), .unk], 0⟩,
    callMutant)

/-- **C1 control (concrete)**: a CALL claimed at the proxy's DELEGATECALL site fails `Cert.check`. -/
theorem proxy_cert_call_mutant_rejected : Cert.check code mutant = false := by
  decide +kernel

end Blanc.Lift.Usdc.Proxy
