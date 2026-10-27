import Blanc.LogBloom
import Blanc.ExecutionBlockCommitments

/-! A checked header bloom excludes addresses from this original execution's
block logs. Identifying an observed historical header remains a consumer duty. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- Membership in the original block logs forces the address's bloom bits in
the header checked by the very same configured transition. -/
theorem ConfiguredBlockTraceIn.containsAddress_of_log_mem
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    {log : Log} (member : log ∈ trace.blockOutput.blockLogs) :
    LogBloom.ContainsAddress trace.block.header.bloom log.address := by
  rw [trace.bloom]
  exact LogBloom.containsAddress_of_mem member

/-- A missing required address bit in the original checked header excludes
that address from every log in the original block output. -/
theorem ConfiguredBlockTraceIn.address_ne_of_bloom_missing
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) {address : Adr}
    (missing : ¬ LogBloom.ContainsAddress trace.block.header.bloom address)
    {log : Log} (member : log ∈ trace.blockOutput.blockLogs) :
    log.address ≠ address := by
  intro same
  exact missing (same ▸ trace.containsAddress_of_log_mem member)

end Blanc.ExecutionTrace
