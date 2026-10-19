import Blanc.Lift.CallProfileTransport
import Blanc.Composition.Curve3Pool3CrvWorld
import Blanc.Lift.Curve3Pool.LivePremises
import Blanc.Lift.MutableCallPost
import Blanc.Lift.VyperNonreentrantDeployed.Token20.RunTransferFrom

/-!
# Compatibility names for the pool's all-gas coin call sites

The generic site definitions and crossing are owned by `Blanc.Lift.AllGasCall` in
`CallProfileTransport.lean`. These names preserve the existing pool call-site API.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift

section Cross

variable (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256)

def ccExt : Nat := AllGasCall.ext b S M G ii is oi

def ccAcc : Nat := AllGasCall.access b S M G t

def ccFwd : Nat := AllGasCall.forwarded b S M G t ii is oi

def ccWarm : Devm := AllGasCall.warmed b S M G t

def ccParent : Devm := AllGasCall.parent b S M G t ii is oi

def ccMsg : Msg := AllGasCall.message sevm b S M G t ii is oi

def ccPost (cpost : Devm) : Devm := AllGasCall.resume b S M G t ii is oi cpost

end Cross

theorem cc_fwd_le (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256) :
    ccFwd b S M G t ii is oi ≤ G - ccExt b S M G ii is oi - ccAcc b S M G t := AllGasCall.forwarded_le b S M G t ii is oi

theorem cc_cross {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {t ii is oi : B256} {cpost : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hdel : getDelegatedCodeAddress (b.state.getCode t.toAdr) = none)
    (hdepth : sevm.depth ≠ 0) (hprec : sevm.benvStat.rules.isPrecomp t.toAdr = false)
    (hroom : S.length < 1024) (hG : G < 2 ^ 256)
    (hcharge : ccAcc b S M G t + ccExt b S M G ii is oi ≤ G)
    (hexec : exec (initEvm (ccMsg sevm b S M G t ii is oi)) = .ok cpost)
    (herr : cpost.error = none) :
    Ninst.RunCompiled sevm (St b (Nat.toB256 G :: t :: 0 :: ii :: is :: oi :: 0x20 :: S) M G)
      (.exec .call) (ccPost b S M G t ii is oi cpost) :=
  AllGasCall.cross hfork hdel hdepth hprec hroom hG hcharge hexec herr

end Blanc.Composition.Curve3Pool3CrvInstance
