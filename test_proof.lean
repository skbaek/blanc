import Blanc.NewCommon
lemma test (x : UInt8) : (x.highs <<< 4) ||| x.lows = x := by
  decide
