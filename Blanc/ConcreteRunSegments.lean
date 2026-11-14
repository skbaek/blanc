import Blanc.ConcreteRunKept

/-! Composable continuing prefixes of the original interpreter, with their
retained frames at every address. This adds no execution relation. -/

namespace Blanc.ConcreteRun

open Jaune

/-- A prefix that extends any original continuation and accounts for exactly
the kept frames contributed by that prefix, independently of the outcome. -/
structure KeptSegment (start stop : Evm) where
  extend : ∀ {out : Execution},
    Jaune.Exec stop.pc stop.sta stop.dyna out →
      Jaune.Exec start.pc start.sta start.dyna out
  frames : Adr → List Jaune.Exec.Frame
  kept : ∀ (a : Adr) {out : Execution}
    (tail : Jaune.Exec stop.pc stop.sta stop.dyna out),
    Blanc.Exec.keptAt a (extend tail) = frames a ++ Blanc.Exec.keptAt a tail

namespace KeptSegment

def trans {s m t : Evm} (left : KeptSegment s m) (right : KeptSegment m t) :
    KeptSegment s t where
  extend tail := left.extend (right.extend tail)
  frames a := left.frames a ++ right.frames a
  kept a _ tail := by rw [left.kept, right.kept, List.append_assoc]

def ofStepN {s t : Evm} (n : Nat) (checked : stepN n s = some t) : KeptSegment s t where
  extend tail := Exec.ofStepN n checked tail
  frames _ := []
  kept a _ tail := by
    exact Exec.keptAt_ofStepN a n checked tail

/-- Compose the actual spawn, entry, child execution and settled resume. The
commit premise is about the settlement, with its original fork behavior. -/
def settled {pc pc' : Nat} {s : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Jaune.Resume} {child : Evm} {raw : Execution}
    (spawn : Evm.step ⟨pc, s, pre⟩ = .spawn frame resume pc')
    (enter : frame.enter = .run child)
    (run : Jaune.Exec child.pc child.sta child.dyna raw)
    (resumed : resume.run (frame.settle raw) = .ok post)
    (commits : Frame.settlementCommits frame raw = true) :
    KeptSegment ⟨pc, s, pre⟩ ⟨pc', s, post⟩ where
  extend tail := .runOk spawn enter run resumed tail
  frames a := if child.sta.currentTarget = a then
      [Jaune.Exec.Frame.ofRun run (Frame.raw_commits_of_settlementCommits commits)]
    else Blanc.Exec.keptAt a run
  kept a _ tail := by
    rw [Blanc.Exec.keptAt, dite_eq_left commits]

end KeptSegment
end Blanc.ConcreteRun
