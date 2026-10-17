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

/-- **Generic composition lemma (segment form of `Ledger.run_holder`).**  Along any run of the book
whose intermediate ledgers are good, a holder with no allowance whose own calls are holder-safe
loses at most its declared debits, and still has no allowance. -/
theorem BookLaws.run_holder {B : Book} (laws : BookLaws B) {h : Adr} :
    ∀ {as : List Sevm} {l l' : B.Ledger},
      B.run l as = some l' →
      (∀ n pre, n < as.length → B.run l (as.take n) = some pre → B.Good pre) →
      (∀ g, B.allow l h g = 0) →
      (∀ a ∈ as, a.caller = h → (B.op a).HolderSafe) →
      B.bal l h ≤ B.bal l' h + ((as.filter fun a => decide (a.caller = h)).map
        fun a => (B.op a).debit h).sum ∧
      ∀ g, B.allow l' h g = 0 := by
  intro as
  induction as with
  | nil =>
    intro l l' hrun _ hz _
    simp only [Book.run, Option.some.injEq] at hrun
    subst hrun
    exact ⟨Nat.le_add_right _ _, hz⟩
  | cons a as ih =>
    intro l l' hrun hgood hz hsafe
    simp only [Book.run] at hrun
    cases hs : B.step l a with
    | none => rw [hs, Option.bind_none] at hrun; cases hrun
    | some m =>
      rw [hs, Option.bind_some] at hrun
      have gl : B.Good l := hgood 0 l (Nat.zero_lt_succ _) rfl
      have hzm : ∀ g, B.allow m h g = 0 := by
        intro g
        by_cases hc : a.caller = h
        · have := laws.allow_safe (g := g) gl hs hc (hsafe a List.mem_cons_self hc)
          rw [hz g] at this
          exact Nat.le_zero.mp this
        · have hle : B.allow m h g ≤ B.allow l h g :=
            Nat.not_lt.mp fun hlt => hc (laws.allow_owner gl hs hlt)
          rw [hz g] at hle
          exact Nat.le_zero.mp hle
      obtain ⟨ihb, iha⟩ := ih hrun (fun n pre hn hpre => hgood (n + 1) pre (Nat.succ_lt_succ hn)
          (by simp only [List.take_succ_cons, Book.run, hs, Option.bind_some]; exact hpre))
        hzm (fun a' ha' => hsafe a' (List.mem_cons_of_mem a ha'))
      refine ⟨?_, iha⟩
      by_cases hc : a.caller = h
      · have hd := laws.holder_debit gl hs hc (hsafe a List.mem_cons_self hc)
        simp only [List.filter_cons, hc, decide_true, ite_true, List.map_cons, List.sum_cons]
        omega
      · have hle : B.bal l h ≤ B.bal m h := Nat.not_lt.mp fun hlt => by
          rcases laws.holder_only gl hs hlt with h1 | h1
          · exact hc h1
          · rw [hz] at h1; exact Nat.lt_irrefl 0 h1
        simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false]
        omega

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
