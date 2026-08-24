import Blanc.ForwardCall

namespace Blanc

open Jaune

set_option linter.unusedTactic false

-- EXPECT: runcompiled-construction
example {fs : List Func} {sevm : Sevm} {pre post : Devm} {f : Func}
    (run : Func.RunCompiled fs sevm pre f post) :
    Func.RunCompiled fs sevm pre f post := by
  blanc_suggest
  exact run

-- EXPECT: runcompiled-construction
example {fs : List Func} {sevm : Sevm} {pre : Devm} {f : Func}
    {out : Execution} (run : Func.RunCompiledTo fs sevm pre f out) :
    Func.RunCompiledTo fs sevm pre f out := by
  blanc_suggest
  exact run

-- EXPECT: line-run-split
example {sevm : Sevm} {pre post : Devm} {line : Line} :
    Line.Run sevm pre line post → True := by
  blanc_suggest
  intro _
  trivial

-- EXPECT: func-run-prefix-split
example {fs : List Func} {sevm : Sevm} {pre post : Devm} {f : Func} :
    Func.Run fs sevm pre f post → True := by
  blanc_suggest
  intro _
  trivial

-- EXPECT: function-observation-invariance
example {f : Func} (inv : Func.Inv Devm.getBal Devm.getBal f) :
    Func.Inv Devm.getBal Devm.getBal f := by
  blanc_suggest
  exact inv

-- EXPECT: successor-projection-normalization
example (devm : Devm) (mach : Mach) (address : Adr) (key : B256) :
    (devm.setMach mach).getStorVal address key = devm.getStorVal address key := by
  blanc_suggest
  rfl

-- EXPECT: devm-projection-bridge
example (devm : Devm) (mach : Mach) :
    (devm.setMach mach).refundCounter = devm.refundCounter := by
  blanc_suggest
  rfl

-- EXPECT: devm-projection-bridge
example (devm : Devm) (mach : Mach) : (devm.setMach mach).mach = mach := by
  blanc_suggest
  rfl

-- EXPECT: devm-projection-bridge
example (devm : Devm) (output : Bytes) :
    (devm.withOutput output).refundCounter = devm.refundCounter := by
  blanc_suggest
  rfl

-- EXPECT: bytesize-composition
example : Func.stop.compileShape.byteSize = 1 := by
  blanc_suggest
  decide

-- EXPECT: bytesize-composition
example : Func.stop.compileShape.byteSize ≠ 0 := by
  blanc_suggest
  decide

-- EXPECT: bytesize-composition
example : Func.stop.compileShape.byteSize ≤ 1 := by
  blanc_suggest
  decide

-- EXPECT: bytesize-composition
example : Func.stop.compileShape.byteSize < 2 := by
  blanc_suggest
  decide

-- EXPECT-NO-MATCH
example (f : Func) : f.compileShape.byteSize = f.compileShape.byteSize := by
  blanc_suggest
  rfl

-- EXPECT-NO-MATCH
example (devm : Devm) (output : Bytes) :
    (devm.withOutput output).pop = (devm.withOutput output).pop := by
  blanc_suggest
  rfl

-- EXPECT-NO-MATCH
example (proposition : Prop) (proof : proposition) : proposition := by
  blanc_suggest
  exact proof

end Blanc
