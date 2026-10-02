import Blanc.Lift.Exact
import Blanc.Lift.HistoryStorage.Check

namespace Blanc.Lift.HistoryStorage

open Jaune

theorem jumps_0 :
    jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  decide

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  unfold Cert.jumpsOk
  rw [List.all_eq_true]
  intro p hp
  simp only [cert, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  simpa only using jumps_0

end Blanc.Lift.HistoryStorage
