import Blanc.ExecutionKeptBalSilent
import Blanc.Corpus.Freeze.BeaconRoots
import Blanc.Corpus.Freeze.HistoryStorage
import Blanc.Lift.SystemExecution.BeaconRoots.Check
import Blanc.Lift.SystemExecution.HistoryStorage.Check

/-!
# Ring-contract value retention

The canonical beacon-roots and history-storage certificates are balance-silent.
The shared kept-history cover therefore proves both frozen S6 cells, including
the value carried by successful reads. The frozen covered-fork premise is
retained; the shared theorem does not need it.
-/

namespace Blanc.Corpus.Proofs

open Jaune Blanc.Lift Blanc.Corpus.Freeze

namespace R
open Blanc.Corpus.Freeze.BeaconRoots
open Blanc.Lift.SystemExecution.BeaconRoots

/-- Exact frozen R-S6: every settled frame's carried value is retained. -/
theorem r_s6 : R_S6 := by
  intro cfg start stop blocks history _covered code senders roots credits
  exact history.systemContract_bal_covers
    (p := (beaconRootsAddress, beaconRootsCode)) (c := cert) (S := [0])
    (by simp only [systemContracts, List.mem_cons, true_or])
    cert_check (progNoExec_of_all (by decide +kernel))
    (by decide +kernel) (by decide +kernel) code senders roots credits

end R

namespace H
open Blanc.Corpus.Freeze.HistoryStorage
open Blanc.Lift.SystemExecution.HistoryStorage

/-- Exact frozen H-S6: every settled frame's carried value is retained. -/
theorem h_s6 : H_S6 := by
  intro cfg start stop blocks history _covered code senders roots credits
  exact history.systemContract_bal_covers
    (p := (historyStorageAddress, historyStorageCode)) (c := cert) (S := [0])
    (by simp only [systemContracts, List.mem_cons, true_or, or_true])
    cert_check (progNoExec_of_all (by decide +kernel))
    (by decide +kernel) (by decide +kernel) code senders roots credits

end H
end Blanc.Corpus.Proofs
