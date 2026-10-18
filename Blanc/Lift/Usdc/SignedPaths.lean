import Blanc.Lift.Usdc.ImplFp
import Blanc.Lift.Usdc.SignedPathsAuth
import Blanc.Lift.Usdc.SignedPathsPermit

/-!
# F7b: no successful implementation frame is signed by the Pair (`impl_signed_not_ok`)

A successful frame of the USDC implementation runs its certificate under the free-pointer step
relation (`implRun_fp`), which is a `SiteStep` (`siteStep_fp`).  A frame the book reads as signed
by `pair` decodes to one of the eight signed entry points (`usdcSigner`): permit, the two
`…WithAuthorization` families and `cancelAuthorization`, each in its `(v, r, s)` and `bytes` form.
The preamble and the dispatcher lead each to its wrapper, and the re-walks of
`SignedPathsAuth.lean` / `SignedPathsPermit.lean` reach one of F7a's two library call sites with
the decoded signer (calldata word 4) as the signer word, where the library rejects the Pair.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.FreePtr

/-- **No successful implementation frame is signed by the Pair** (the two library call sites:
entry 111's `_requireValidSignature`, copy loop 117; permit's inline call in entry 9, copy loop
80): the free pointer read before each encoding is good (F5), the walk from that read to the
`DELEGATECALL` keeps the signer word at input byte `4` (F4 for the copy loop), the library child
returns `false` (F6), and the read of its output reverts the frame. -/
theorem impl_signed_not_ok {P pair : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post)) (code : sevm.code = Impl.code)
    (fork : CoveredFork sevm.benvStat.fork) (hsg : sevm.benvStat.rules.stateGas = none)
    (target : sevm.currentTarget = P) (hmem : pre.memory = Mem.empty) (hstack : pre.stack = [])
    (hpot : pre.gasMeasure < 2 ^ 256)
    (libCode : pre.getCode usdcLib = Lib.code)
    (pairCode : pre.getCode pair = UniswapV2Pair.code)
    (notPre : ¬ sevm.benvStat.rules.isPrecomp pair)
    (rejects : LibRejects pair) (signed : (usdcBookS P).signer sevm = some pair) : False := by
  subst target
  have hP : SiteStep (FpStep (PotStep (StepIn ⟨0, sevm, pre, .ok post, run⟩))) := siteStep_fp
  obtain ⟨f, hf, frun⟩ := implRun_fp run code fork hsg hmem hpot
  obtain rfl : f = Impl.t_0000_c0 := (Option.some.inj hf).symm
  have h := SFunc.runP_iff_runCutP_nil.mp frun
  generalize FpStep (PotStep (StepIn ⟨0, sevm, pre, .ok post, run⟩)) = Q at hP h
  rw [St.self (d := pre) hstack rfl] at h
  obtain ⟨M', G', h⟩ := preambleP hP fork h
  change usdcSigner sevm = some pair at signed
  unfold usdcSigner at signed
  split at signed
  · rename_i o s v hdec
    obtain ⟨sel, ho, -⟩ := decode_permit hdec
    have hsg' : (Sevm.dataWord sevm 4).toAdr = pair := ho ▸ Option.some.inj signed
    rcases sel with sel | sel
    · exact path_permitBytes hP fork rejects notPre libCode pairCode sel hsg' h
    · exact path_permitVrs hP fork rejects notPre libCode pairCode sel hsg' h
  · rename_i s d v n hdec
    obtain ⟨sel, ho, -⟩ := decode_twa hdec
    have hsg' : (Sevm.dataWord sevm 4).toAdr = pair := ho ▸ Option.some.inj signed
    rcases sel with sel | sel
    · exact path_twaBytes hP fork rejects notPre libCode pairCode hsg' sel h
    · exact path_twaVrs hP fork rejects notPre libCode pairCode hsg' sel h
  · rename_i s d v n hdec
    obtain ⟨sel, ho, -⟩ := decode_rwa hdec
    have hsg' : (Sevm.dataWord sevm 4).toAdr = pair := ho ▸ Option.some.inj signed
    rcases sel with sel | sel
    · exact path_rwaBytes hP fork rejects notPre libCode pairCode hsg' sel h
    · exact path_rwaVrs hP fork rejects notPre libCode pairCode hsg' sel h
  · rename_i a n hdec
    obtain ⟨sel, ho, -⟩ := decode_cancel hdec
    have hsg' : (Sevm.dataWord sevm 4).toAdr = pair := ho ▸ Option.some.inj signed
    rcases sel with sel | sel
    · exact path_cancelBytes hP fork rejects notPre libCode pairCode sel hsg' h
    · exact path_cancelVrs hP fork rejects notPre libCode pairCode sel hsg' h
  · cases signed

end Blanc.Lift.Usdc
