import Blanc.Semantics
import Jaune.Transaction
import Jaune.ExecSettlement

/-!
The contract-neutral committed-execution and complete frame-settlement
traversal (`Jaune.Frame.settlementCommits`, `Jaune.Exec.descendantFrames`,
`Jaune.Exec.committedFrames` and their theorems) is owned by Jaune's
`Jaune.ExecSettlement`, imported here.  This module keeps the small
checked-to-unchecked system-transaction bridge shared by invariant and retained
trace consumers, which needs `Jaune.Transaction`.
-/

namespace Blanc

open Jaune

-- Compatibility names for published statements that quote the pre-adoption
-- names: the claim pin in `scripts/ClaimCheck.lean` (`Blanc.Frame.settlementCommits`)
-- and the frozen public WETH10 statement headers (all four names).  `export`
-- aliases, not new declarations: each resolves to the `Jaune.*` declaration
-- itself.
namespace Frame
export Jaune.Frame (settlementCommits raw_commits_of_settlementCommits)
end Frame

namespace Exec
export Jaune.Exec (committedFrames descendantFrames)
end Exec

/-- A successful checked system transaction exposes the same successful raw
message result used by generic invariant and retained-trace consumers. -/
lemma processCheckedSystemTransaction_to_unchecked {benv : Benv}
    {target : Adr} {data : Bytes} {st : Jaune.State} {out : MsgCallOutput}
    (h : processCheckedSystemTransaction benv target data = .ok ⟨st, out⟩) :
    processUncheckedSystemTransaction benv target data = .ok ⟨st, out⟩ := by
  dsimp [processCheckedSystemTransaction, processUncheckedSystemTransaction] at h ⊢
  split at h
  · cases h
  · rcases Except.bind_eq_ok h with ⟨⟨st', out'⟩, h1, h2⟩
    split at h2
    · cases h2
    · obtain ⟨h3, h4⟩ := Prod.mk.inj (Except.ok.inj h2)
      rw [Except.mapError_eq_ok_iff] at h1
      subst h3; subst h4; exact h1

end Blanc
