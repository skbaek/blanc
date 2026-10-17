import Blanc.Composition.UniswapV2PairWeth9Checkpoint
import Blanc.Lift.Weth9.FiniteFootprint
import Blanc.Lift.UniswapV2Pair.FiniteCheckpoint

/-!
# A computable checker for the joint checkpoint

`checkJoint pair weth wrows prows base side w` decides `JointCheckpoint` over a finite description:
WETH9's tracked keys are the keys of `wrows` (each with its slot word), the Pair's tracked keys are
the keys of `prows` (each with its slot word and value), and the Pair's model state is
`rowsState base prows`.  It checks both codes byte for byte, the Pair's storage representation
(`checkPair`), the token and lock fields, WETH9's footprint invariant (`checkFoot`), the world's
balance sum over its actual accounts (`checkSumNof`), the Pair's WETH9 balance row against the
reserve and its allowance rows (`checkHolder`), and `pair ≠ weth`.  `checkJoint_sound` is the
soundness theorem.

Cost: linear in the rows and storage entries of the two contracts and in the world's accounts (plus
one storage lookup per row and one keccak per row for its slot word), and linear in the two code
lengths.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.FiniteCheckpoint Blanc.Lift.Weth9 Blanc.Lift.UniswapV2Pair

/-- Code identity, compared on the byte arrays' lists. -/
theorem image_of_data {c d : ByteArray} (h : c.data.toList = d.data.toList) :
    some c.toList = some d.toList := by
  rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data, h]

/-- **The joint checkpoint checker.** -/
def checkJoint (pair weth : Adr) (wrows : List (Key × B256)) (prows : List PairRow)
    (base : UniswapV2Pair.State) (side : TokenSide) (w : Jaune.State) : Bool :=
  decide ((w.getCode pair).data.toList = UniswapV2Pair.code.data.toList) &&
    checkPair prows (w.getStor pair) base &&
    decide (base.tokenOn side = weth) && decide (base.unlocked = 1) &&
    decide ((w.getCode weth).data.toList = Weth9.code.data.toList) &&
    checkFoot wrows (w.getStor weth) (w.bal weth) && checkSumNof w &&
    checkHolder wrows (w.getStor weth) pair (base.reserveOn side) && decide (pair ≠ weth)

/-- **Soundness of the joint checkpoint checker.** -/
theorem checkJoint_sound {pair weth : Adr} {wrows : List (Key × B256)} {prows : List PairRow}
    {base : UniswapV2Pair.State} {side : TokenSide} {w : Jaune.State}
    (h : checkJoint pair weth wrows prows base side w = true) :
    JointCheckpoint pair weth (rowKeys wrows) (pairKeys prows) (rowsState base prows) side w := by
  simp only [checkJoint, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpairCode, hpair⟩, htoken⟩, hunlocked⟩, hwethCode⟩, hfoot⟩, hsum⟩, hholder⟩,
    hapart⟩ := h
  obtain ⟨foot, sound⟩ := checkFoot_sound hfoot
  obtain ⟨tracked, reserve, noAllowance⟩ := checkHolder_sound sound hholder
  exact
    { pairCode := image_of_data hpairCode
      pairRep := checkPair_sound hpair
      token := htoken
      unlocked := hunlocked
      wethCode := image_of_data hwethCode
      wethFoot := foot
      sumNof := checkSumNof_sound hsum
      tracked := tracked
      noAllowance := noAllowance
      reserve := reserve
      apart := hapart }

end Blanc.Composition.UniswapV2PairWeth9Joint
