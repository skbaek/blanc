import Blanc.Lift.BookedSpec
import Blanc.Lift.Weth9.Lift
import Blanc.Lift.Weth9.Spec

/-!
# The WETH9 frame contract

`weth9Sem` is the certified code semantics of the pinned WETH9 runtime: its
image is the deployed bytes and its run relation is the lifted program on a
covered fork, justified by `exec_lift` (gate G1).  `weth9Spec` is the
booked-sum frame contract (`ContractSpecSem.ofBookedSum`) at WETH9's
collision-safe booked total `bookedSum`; its invariant is `Solvent`.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

theorem code_toList_length : code.toList.length = 3124 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

/-- The certified semantics of the pinned WETH9 runtime. -/
def weth9Sem : CodeSem where
  image := some code.toList
  Run sevm pre post := CoveredFork sevm.benvStat.fork → SProg.Run prog sevm pre post
  correct := by
    intro sevm pre post exc hcode hfork
    have h : sevm.code.toList = code.toList := Option.some.inj hcode
    have hc : sevm.code = code := by
      cases hs : sevm.code with
      | mk d =>
        cases hk : code with
        | mk d' =>
          rw [hs, hk] at h
          rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at h
          exact congrArg ByteArray.mk (Array.toList_inj.mp h)
    exact exec_lift hc hfork exc
  ne_nil := by
    intro l hl h
    have h' : code.toList = l := Option.some.inj hl
    have hlen := code_toList_length
    rw [h', h] at hlen
    exact absurd hlen (by decide)
  not_delegation := by
    intro c hc hdel
    have h : c.toList = code.toList := Option.some.inj hc
    have hlen : c.toList.length = 3124 := h ▸ code_toList_length
    rw [ByteArray.toList_eq_toList_data, Array.length_toList] at hlen
    have hsize : c.size = eoaDelegatedCodeLength := hdel.1
    have hsz : c.size = c.data.size := rfl
    rw [hsz, hlen] at hsize
    exact absurd hsize (by decide)

/-- **The WETH9 frame contract**: booked-sum solvency over the lifted runtime. -/
noncomputable def weth9Spec : ContractSpecSem := ContractSpecSem.ofBookedSum weth9Sem bookedSum

theorem weth9Spec_inv : weth9Spec.Inv = Solvent := rfl

theorem weth9Spec_side : weth9Spec.Side = SumNof := rfl

end Blanc.Lift.Weth9
