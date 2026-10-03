import Blanc.Lift.ConsolidationRequest.Cert

namespace Blanc.Lift.ConsolidationRequest

open Jaune

def prog : List SFunc := cert.prog

theorem prog_root : prog[0]? = some t_0000_c0 := rfl

end Blanc.Lift.ConsolidationRequest
