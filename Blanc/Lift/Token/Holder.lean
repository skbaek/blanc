import Blanc.Lift.Token.Core

/-!
# Token interface core: holder and segment laws

Generic consequences of the token core used by the composition: the segment form of the holder
argument over any `Book` satisfying `BookLaws`, and the positional segment between two settled
frames of a history.  Contract-neutral; no storage layout appears.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

theorem Book.run_append (B : Book) :
    ∀ (l : B.Ledger) (xs ys : List Sevm),
      B.run l (xs ++ ys) = (B.run l xs).bind fun m => B.run m ys
  | l, [], ys => by simp only [List.nil_append, Book.run, Option.bind_some]
  | l, a :: xs, ys => by
    simp only [List.cons_append, Book.run]
    cases B.step l a with
    | none => rfl
    | some m => simp only [Option.bind_some]; exact Book.run_append B m xs ys

theorem entryAsks_append (T : Adr) (xs ys : List Exec.Frame) :
    entryAsks T (xs ++ ys) = entryAsks T xs ++ entryAsks T ys := by
  simp only [entryAsks, List.filter_append, List.map_append]

/-- **Positional segment.**  Between two settled positions `i < j` of a history, the booked ledger at
`j` is the book run, from the ledger at `i`, over exactly the entered writer frames between them. -/
theorem Core.segment {T : Adr} {B : Book} (C : Core T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : C.Hist tr) {pre mid post : List Exec.Frame} {f g : Exec.Frame}
    (split : tr.settledFrames = pre ++ f :: mid ++ g :: post) :
    B.run (C.ledgerOf tr f.pre.state) (entryAsks T (f :: mid)) =
      some (C.ledgerOf tr g.pre.state) := by
  have atF := C.replayAt tr hist pre f (mid ++ g :: post) (by
    rw [split, List.append_assoc, List.cons_append])
  have atG := C.replayAt tr hist (pre ++ f :: mid) g post split
  rw [entryAsks_append, Book.run_append, atF, Option.bind_some] at atG
  exact atG

end Blanc.Lift.Token
