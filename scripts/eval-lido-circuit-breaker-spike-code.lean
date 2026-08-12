-- Emit the exact integrated feasibility-spike runtime.  This evaluator owns no
-- runtime literal or proof; `LidoCircuitBreakerSpike.spikeCode_compile_official`
-- is the compiler witness.

import Blanc.LidoCircuitBreakerSpike

namespace Blanc.LidoCircuitBreakerSpike

open Jaune

#eval show IO Unit from do
  match Prog.compile (spike officialParams) with
  | none => throw (IO.userError "Lido CircuitBreaker spike compilation failed")
  | some code =>
      IO.println s!"official {code.length} {code.toHex}"
      IO.println s!"sha256 {code.sha256.toHex}"
      IO.println s!"keccak256 {code.keccak.toHex}"
      IO.println s!"eip170-headroom {24576 - code.length}"
      IO.println s!"initcode-estimate {initcodeSizeEstimate}"
      IO.println s!"eip3860-estimate-headroom {49152 - initcodeSizeEstimate}"
      IO.println s!"source-sstore-sites {progSourceSstoreSiteCount (spike officialParams)}"
      IO.println s!"source-tstore-sites {progSourceTstoreSiteCount (spike officialParams)}"
      IO.println s!"source-external-call-sites {progSourceExternalCallSiteCount (spike officialParams)}"
      IO.println s!"enum-cycle-certificate {closedReadOnly (spike officialParams) enumCertificate}"
      IO.println s!"enum-writing-mutant {closedReadOnly (enumMutantProgram officialParams) enumCertificate}"

end Blanc.LidoCircuitBreakerSpike
