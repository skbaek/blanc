import Blanc.Composition.Corpus.Proofs.RingHistory

/-! Conditional observation-root endpoints. These theorems consume the exact
frozen observation structures; they do not construct or adopt an observation. -/

namespace Blanc.Corpus.Proofs.RingRoots

open Jaune Blanc Blanc.Corpus.Freeze

/-- Exact conditional R-S4, from R-S3 and the existing mainnet schedule theorem. -/
theorem r_s4 : BeaconRoots.R_S4 := by
  intro checkpoint final blocks history obs clean
  exact RingHistory.R.r_s3 history history.mainnet_covered obs.code obs.systemEmpty clean

/-- Exact conditional H-S4, with the same supplied checkpoint observation. -/
theorem h_s4 : HistoryStorage.H_S4 := by
  intro checkpoint final blocks history obs clean
  exact RingHistory.H.h_s3 history history.mainnet_covered obs.code obs.systemEmpty clean

end Blanc.Corpus.Proofs.RingRoots
