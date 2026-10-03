import Blanc.Lift.Exact
import Blanc.Lift.CheckAssembly
import Blanc.Lift.ConsolidationRequest.Check

namespace Blanc.Lift.ConsolidationRequest

open Jaune

theorem code_eq : code = Blanc.consolidationRequestCode := by
  rfl

theorem jumps_0 :
    jumpsOkNode code (Cert.entries cert) t_0000_c0 [] = true := by
  decide +kernel
theorem jumps_1 :
    jumpsOkNode code (Cert.entries cert) t_00e7_c1 [.unk, .unk, .unk] = true := by
  decide +kernel
theorem jumps_2 :
    jumpsOkNode code (Cert.entries cert) t_0146_c2 [.unk] = true := by
  decide +kernel
theorem jumps_3 :
    jumpsOkNode code (Cert.entries cert) t_0173_c3 [.unk, .unk] = true := by
  decide +kernel
theorem jumps_4 :
    jumpsOkNode code (Cert.entries cert) t_018e_c4 [.unk, .unk] = true := by
  decide +kernel
theorem jumps_5 :
    jumpsOkNode code (Cert.entries cert) t_004d_c5 [.unk, .unk, .unk, .unk, .unk] = true := by
  decide +kernel
theorem jumps_6 :
    jumpsOkNode code (Cert.entries cert) t_00e9_c6 [.unk, .unk, .unk, .unk] = true := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true :=
  Cert.jumpsOk_seven jumps_0 jumps_1 jumps_2 jumps_3 jumps_4 jumps_5 jumps_6

end Blanc.Lift.ConsolidationRequest
