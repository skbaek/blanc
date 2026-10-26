import Blanc.Lift.FreePtrSound
import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.Usdc.ImplFp.Check

/-! The USDC implementation passes the free-pointer check (unit F5).

`impl_fpCert` assembles the generated per-entry kernel decisions
(`ImplFp/Check<i>.lean`, chained in `ImplFp/Check.lean`; producer
`scripts/lift/fp_annot.py`, registered in `scripts/lift/certificates.json`), and
`implRun_fp` instantiates `lift_sound_fp` with it and the certificate's own check. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.FreePtr Blanc.Lift.Usdc.ImplFp

/-- **The implementation passes the free-pointer check** (generated, one kernel decide per
entry, in four entry-group modules). -/
theorem impl_fpCert : fpCert Impl.cert implFpAnn = true :=
  fpCert_of_fpFrom (by decide +kernel) fp_rest_0

/-- The USDC implementation's runs, with the observation. -/
theorem implRun_fp {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Impl.code) (fork : CoveredFork sevm.benvStat.fork)
    (hsg : sevm.benvStat.rules.stateGas = none) (hmem : pre.memory = Mem.empty)
    (hpot : pre.gasMeasure < 2 ^ 256) :
    SProg.RunP (FpStep (PotStep (StepIn ⟨0, sevm, pre, .ok post, run⟩))) Impl.cert.prog sevm pre
      post :=
  lift_sound_fp Impl.cert_check impl_fpCert code fork hsg hmem hpot run

/-- The implementation's observed run under the actual rules without state gas. -/
theorem implRun_fp_noStateGas {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (hsg : sevm.benvStat.rules.stateGas = none) (hmem : pre.memory = Mem.empty)
    (hpot : pre.gasMeasure < 2 ^ 256) :
    SProg.RunP (FpStep (PotStep (StepIn ⟨0, sevm, pre, .ok post, run⟩)))
      Impl.cert.prog sevm pre post :=
  lift_sound_fp_noStateGas Impl.cert_check impl_fpCert code hsg hmem hpot run

end Blanc.Lift.Usdc
