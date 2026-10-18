import Blanc.Lift.FrameWalkCut
import Blanc.Lift.Curve3Pool.LivePremises

/-!
# The pool's call premises read off the actual derivation

`xa_staticWordOkAt`: at a walked `STATICCALL` site whose state is one the premise
`StaticWordOkAt` speaks about (a `W` world, enough gas, the input window), the frame's next
direct child is that call, and its first return word is the premise's answer. With the cut walk
(`xa_cutAt_start`), the reply a forward run consumed is the reply the produced execution's child
gave, which is what the environment of the safety theorems reads (`EnvOf.supply`'s `ReplyAt`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- **A premised `STATICCALL` at a walked site is the next child** (see the module note). -/
theorem xa_staticWordOkAt {sevm : Sevm} {post b : Devm} {M : Mem} {pc G U : Nat}
    {t A ii is oi : B256} {data : Bytes} {S : List B256} {L : List Exec.Frame}
    {W W' : Devm → Prop} (fork : CoveredFork sevm.benvStat.fork)
    (hat : Ninst.At sevm.code pc (.exec .staticcall))
    (h : XAt sevm post pc (St b (Nat.toB256 G :: t :: ii :: is :: oi :: 0x20 :: S) M G) L)
    (hp : StaticWordOkAt sevm W W' t data A U ii is oi) (hW : W b) (hU : U ≤ G)
    (hG : G < 2 ^ 256) (hin : (M.read ii.toNat is.toNat).1 = data)
    (hpc : ¬ sevm.benvStat.rules.isPrecomp t.toAdr) :
    ∃ c L', L = c :: L' ∧ c.sevm.currentTarget = t.toAdr ∧ c.sevm.data = data ∧
      32 ≤ c.post.output.length ∧ Bytes.toB256 (c.post.output.take 32) = A := by
  obtain ⟨d, out, hrun, hpost, hlen, -, hA, -⟩ := hp b S M G hW hU hG hin
  obtain ⟨c, L', hL, -, hch⟩ := xa_staticcall_runCompiled fork hat rfl h hrun hpost.stack
    (by decide) hpc
  refine ⟨c, L', hL, hch.target, ?_, ?_, ?_⟩
  · rw [hch.data]; exact hin
  · rw [hch.output, hpost.returnData]; exact hlen
  · rw [hch.output, hpost.returnData]; exact hA

end Blanc.Lift.Curve3Pool
