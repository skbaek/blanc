-- Genuine DRIP arithmetic observations for the independent Python comparator.
-- No golden answers, Python model, runtime execution or theorem premise.
import Blanc.DripRpow

namespace Blanc.Drip.ArithmeticEvaluation

open Jaune Lean

private abbrev s : Nat := scale.toNat
private abbrev h : Nat := half.toNat
private abbrev x : Nat := rate.toNat

/-- Trace the fixed-rate runtime order using public rounded multiplication.
The independent comparator uses a bit table instead of this descending loop. -/
private def operationTrace (elapsed : Nat) : Array String × Nat := Id.run do
  let mut n := elapsed / 2
  let mut z := if elapsed % 2 = 1 then x else s
  let mut base := x
  let mut kinds : Array String := #[]
  let mut largest := 0
  for _ in List.range (binaryDepth (elapsed / 2)) do
    largest := max largest (base * base)
    base := Jaune.mulr s h base base
    kinds := kinds.push "square"
    if n % 2 = 1 then
      largest := max largest (z * base)
      z := Jaune.mulr s h z base
      kinds := kinds.push "multiply"
    n := n / 2
  return (kinds, largest)

private def factorRow (k : Nat) : _root_.Lean.Json :=
  let trace := operationTrace k
  _root_.Lean.Json.mkObj [
    ("id", _root_.Lean.Json.str s!"factor/{k}"),
    ("input", _root_.Lean.Json.mkObj [("base", _root_.Lean.Json.str (toString x)), ("elapsed", _root_.Lean.Json.str (toString k))]),
    ("result", _root_.Lean.Json.mkObj [
      ("factorNat", _root_.Lean.Json.str (toString (factorNat k))),
      ("rpow", _root_.Lean.Json.str (toString (Jaune.rpow s h x k))),
      ("word", _root_.Lean.Json.str (toString ((B256.rpow scale half rate k).toNat))),
      ("depth", _root_.Lean.Json.str (toString (binaryDepth (k / 2)))),
      ("weight", _root_.Lean.Json.str (toString (binaryWeight (k / 2)))),
      ("operationCount", _root_.Lean.Json.str (toString (rpowOps x k))),
      ("operationKinds", _root_.Lean.Json.arr (trace.1.map _root_.Lean.Json.str)),
      ("largestProduct", _root_.Lean.Json.str (toString trace.2))])]

private def zeroRow (k : Nat) : _root_.Lean.Json :=
  _root_.Lean.Json.mkObj [
    ("id", _root_.Lean.Json.str s!"zero/{k}"),
    ("input", _root_.Lean.Json.mkObj [("base", _root_.Lean.Json.str "0"), ("elapsed", _root_.Lean.Json.str (toString k))]),
    ("result", _root_.Lean.Json.mkObj [
      ("rpow", _root_.Lean.Json.str (toString (Jaune.rpow s h 0 k))),
      ("word", _root_.Lean.Json.str (toString ((B256.rpow scale half 0 k).toNat)))])]

private def roundingRow (delta : Int) : _root_.Lean.Json :=
  let right := (Int.ofNat h + delta).toNat
  _root_.Lean.Json.mkObj [
    ("id", _root_.Lean.Json.str s!"round/{delta}"),
    ("input", _root_.Lean.Json.mkObj [("left", _root_.Lean.Json.str "1"),
      ("right", _root_.Lean.Json.str (toString right)), ("offset", _root_.Lean.Json.str (toString h))]),
    ("result", _root_.Lean.Json.mkObj [
      ("mulr", _root_.Lean.Json.str (toString (Jaune.mulr s h 1 right))),
      ("residue", _root_.Lean.Json.str (toString (mulrResidue s h 1 right)))])]

/-- Public expanded-tree fields at the fixed DRIP scale/rate. -/
private def treeFields (tree : RoundTree) (initial : Nat) : _root_.Lean.Json :=
  _root_.Lean.Json.mkObj [
    ("eval", _root_.Lean.Json.str (toString (tree.eval s x initial))),
    ("nodes", _root_.Lean.Json.str (toString tree.nodes)),
    ("baseCount", _root_.Lean.Json.str (toString tree.baseCount)),
    ("scaleCount", _root_.Lean.Json.str (toString tree.scaleCount)),
    ("initialCount", _root_.Lean.Json.str (toString tree.initialCount)),
    ("ideal", _root_.Lean.Json.str (toString (tree.ideal s x initial))),
    ("scaled", _root_.Lean.Json.str (toString (tree.scaled s x initial))),
    ("exactUnder", _root_.Lean.Json.str (toString (tree.exactUnder s x initial))),
    ("exactOver", _root_.Lean.Json.str (toString (tree.exactOver s x initial))),
    ("upperError", _root_.Lean.Json.str (toString (tree.upperError s x initial))),
    ("lowerError", _root_.Lean.Json.str (toString (tree.lowerError s x initial)))]

private def treeRow (k : Nat) : _root_.Lean.Json :=
  _root_.Lean.Json.mkObj [
    ("id", _root_.Lean.Json.str s!"tree/{k}"),
    ("input", _root_.Lean.Json.mkObj [("base", _root_.Lean.Json.str (toString x)),
      ("elapsed", _root_.Lean.Json.str (toString k)), ("initial", _root_.Lean.Json.str "0")]),
    ("result", treeFields (rpowTree h k) 0)]

private def witnessRow (over : Bool) : _root_.Lean.Json :=
  let right := if over then Jaune.mulr s h x x else x
  let value := Jaune.mulr s h x right
  let product := x * right
  let signed := Int.ofNat (s * value) - Int.ofNat product
  _root_.Lean.Json.mkObj [
    ("id", _root_.Lean.Json.str (if over then "witness/over" else "witness/under")),
    ("input", _root_.Lean.Json.mkObj [("left", _root_.Lean.Json.str (toString x)),
      ("right", _root_.Lean.Json.str (toString right)), ("offset", _root_.Lean.Json.str (toString h))]),
    ("result", _root_.Lean.Json.mkObj [("product", _root_.Lean.Json.str (toString product)),
      ("mulr", _root_.Lean.Json.str (toString value)),
      ("residue", _root_.Lean.Json.str (toString (mulrResidue s h x right))),
      ("scaledError", _root_.Lean.Json.str (toString signed))])]

private def segmentRow : _root_.Lean.Json :=
  let left := [3]
  let right := [1, 2]
  let common := segmentCommonScaleCount h left right
  let forward := segmentDriftForward s h x s left right
  let reverse := segmentDriftForward s h x s right left
  _root_.Lean.Json.mkObj [
    ("id", _root_.Lean.Json.str "segment/3-vs-1-2"),
    ("input", _root_.Lean.Json.mkObj [("initialChi", _root_.Lean.Json.str (toString s)),
      ("left", _root_.Lean.Json.arr #[_root_.Lean.Json.str "3"]),
      ("right", _root_.Lean.Json.arr #[_root_.Lean.Json.str "1", _root_.Lean.Json.str "2"])]),
    ("result", _root_.Lean.Json.mkObj [
      ("left", treeFields (segmentTree h left) s),
      ("right", treeFields (segmentTree h right) s),
      ("commonScaleCount", _root_.Lean.Json.str (toString common)),
      ("leftLifted", _root_.Lean.Json.mkObj [
        ("upper", _root_.Lean.Json.str (toString (segmentLiftedUpper s h x s left common))),
        ("lower", _root_.Lean.Json.str (toString (segmentLiftedLower s h x s left common)))]),
      ("rightLifted", _root_.Lean.Json.mkObj [
        ("upper", _root_.Lean.Json.str (toString (segmentLiftedUpper s h x s right common))),
        ("lower", _root_.Lean.Json.str (toString (segmentLiftedLower s h x s right common)))]),
      ("forward", _root_.Lean.Json.str (toString forward)),
      ("reverse", _root_.Lean.Json.str (toString reverse)),
      ("distance", _root_.Lean.Json.str (toString (natDistance
        (segmentIndex s h x s left) (segmentIndex s h x s right)))),
      ("bound", _root_.Lean.Json.str (toString (max forward reverse)))])]

private def outerRow (name : String) (chi k : Nat) : _root_.Lean.Json :=
  _root_.Lean.Json.mkObj [
    ("id", _root_.Lean.Json.str ("outer/" ++ name)),
    ("input", _root_.Lean.Json.mkObj [("chi", _root_.Lean.Json.str (toString chi)), ("elapsed", _root_.Lean.Json.str (toString k))]),
    ("result", _root_.Lean.Json.mkObj [
      ("freshNat", _root_.Lean.Json.str (toString (freshNat chi k))),
      ("compositionResidue", _root_.Lean.Json.str (toString (compositionResidue chi k))),
      ("product", _root_.Lean.Json.str (toString (chi * factorNat k)))])]

/-- Only scalar rows use large exponents; expanded trees are restricted to 0..16. -/
private def response : _root_.Lean.Json :=
  let exponents := [0, 1, 2, 3, 31536000, maxElapsed.toNat]
  let last := (s * (maxChi.toNat + 1) - 1) / factorNat maxElapsed.toNat
  let rows := exponents.map factorRow ++ exponents.map zeroRow ++
    ([-1, 0, 1] : List Int).map roundingRow ++
    (List.range 17).map treeRow ++ [witnessRow false, witnessRow true, segmentRow] ++
    [outerRow "accepted" last maxElapsed.toNat,
     outerRow "rejected" (last + 1) maxElapsed.toNat,
     outerRow "single" s 3, outerRow "split-tail" x 2]
  _root_.Lean.Json.mkObj [
    ("schema", _root_.Lean.Json.num 1),
    ("constants", _root_.Lean.Json.mkObj [("S", _root_.Lean.Json.str (toString s)),
      ("H", _root_.Lean.Json.str (toString h)), ("R", _root_.Lean.Json.str (toString x)),
      ("maxChi", _root_.Lean.Json.str (toString maxChi.toNat)),
      ("maxElapsed", _root_.Lean.Json.str (toString maxElapsed.toNat))]),
    ("rows", _root_.Lean.Json.arr rows.toArray),
    ("done", _root_.Lean.Json.str "drip-arithmetic-v1-complete")]

#eval IO.println response.compress

end Blanc.Drip.ArithmeticEvaluation
