import Blanc.Lift.Token.Holder

/-!
# Token interface core: good ledgers along settled prefixes, and holder segments

Generic consequences of `Core` and `BookLaws`: every ledger the book passes through while replaying
a settled prefix is the booked ledger at some settled frame, hence good (`Core.good_along`); so
`BookLaws.run_holder` (A5 form) applies to any contiguous run of settled frames
(`Core.run_holder_segment`).  Contract-neutral.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

theorem entryAsks_cons (T : Adr) (x : Exec.Frame) (xs : List Exec.Frame) :
    entryAsks T (x :: xs) = entryAsks T [x] ++ entryAsks T xs := by
  rw [← entryAsks_append]
  rfl

open Classical in
theorem entryAsks_single_of_entry {T : Adr} {x : Exec.Frame}
    (h : IsEntry T x ∧ x.sevm.isStatic = false) : entryAsks T [x] = [x.sevm] := by
  simp only [entryAsks, List.filter_cons, List.filter_nil, decide_eq_true h, ite_true,
    List.map_cons, List.map_nil]

open Classical in
theorem entryAsks_single_of_not_entry {T : Adr} {x : Exec.Frame}
    (h : ¬ (IsEntry T x ∧ x.sevm.isStatic = false)) : entryAsks T [x] = [] := by
  simp only [entryAsks, List.filter_cons, List.filter_nil, decide_eq_false h,
    Bool.false_eq_true, ite_false, List.map_nil]

/-- Every proper prefix of a list's entry messages is the entry messages of a prefix ending just
before a frame of the list. -/
theorem entryAsks_take (T : Adr) :
    ∀ (frames : List Exec.Frame) (n : Nat), n < (entryAsks T frames).length →
      ∃ (b1 : List Exec.Frame) (g : Exec.Frame) (b2 : List Exec.Frame),
        frames = b1 ++ g :: b2 ∧ entryAsks T b1 = (entryAsks T frames).take n
  | [], n, h => by
    simp only [entryAsks, List.filter_nil, List.map_nil, List.length_nil] at h
    omega
  | x :: xs, n, h => by
    rw [entryAsks_cons] at h ⊢
    by_cases hx : IsEntry T x ∧ x.sevm.isStatic = false
    · rw [entryAsks_single_of_entry hx] at h ⊢
      cases n with
      | zero => exact ⟨[], x, xs, rfl, rfl⟩
      | succ n =>
        simp only [List.singleton_append, List.length_cons] at h
        obtain ⟨b1, g, b2, eq, asks⟩ := entryAsks_take T xs n (by omega)
        refine ⟨x :: b1, g, b2, by rw [eq]; rfl, ?_⟩
        rw [entryAsks_cons, entryAsks_single_of_entry hx, asks]
        rfl
    · rw [entryAsks_single_of_not_entry hx] at h ⊢
      rw [List.nil_append] at h ⊢
      obtain ⟨b1, g, b2, eq, asks⟩ := entryAsks_take T xs n h
      refine ⟨x :: b1, g, b2, by rw [eq]; rfl, ?_⟩
      rw [entryAsks_cons, entryAsks_single_of_not_entry hx, List.nil_append, asks]

/-- **Every ledger along the replay of a settled prefix is good.** -/
theorem Core.good_along {T : Adr} {B : Book} (C : Core T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : C.Hist tr) {frames rest : List Exec.Frame} (split : tr.settledFrames = frames ++ rest) :
    ∀ n p, n < (entryAsks T frames).length →
      B.run (C.ledgerOf tr checkpoint.state) ((entryAsks T frames).take n) = some p → B.Good p := by
  intro n p h run
  obtain ⟨b1, g, b2, eq, asks⟩ := entryAsks_take T frames n h
  have settled : tr.settledFrames = b1 ++ g :: (b2 ++ rest) := by
    rw [split, eq, List.append_assoc, List.cons_append]
  have at_g := C.replayAt tr hist b1 g (b2 ++ rest) settled
  rw [asks, run] at at_g
  cases Option.some.inj at_g
  exact C.goodAt tr hist g (by rw [settled]; exact List.mem_append_right _ List.mem_cons_self)

/-- **Holder segment.**  Along a contiguous run `mid` of settled frames, from the booked ledger
after the frames before it, a holder with no allowance whose own entries in `mid` are holder-safe
loses at most their declared debits and keeps no allowance. -/
theorem Core.run_holder_segment {T : Adr} {B : Book} (C : Core T B) (laws : BookLaws B)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) (hist : C.Hist tr) {h : Adr}
    {pre mid post : List Exec.Frame} (split : tr.settledFrames = pre ++ mid ++ post)
    {l l' : B.Ledger} (atPre : B.run (C.ledgerOf tr checkpoint.state) (entryAsks T pre) = some l)
    (step : B.run l (entryAsks T mid) = some l') (zero : ∀ g, B.allow l h g = 0)
    (safe : ∀ a ∈ entryAsks T mid, a.caller = h → (B.op a).HolderSafe) :
    B.bal l h ≤ B.bal l' h + (((entryAsks T mid).filter fun a => decide (a.caller = h)).map
      fun a => (B.op a).debit h).sum ∧ ∀ g, B.allow l' h g = 0 := by
  refine laws.run_holder step ?_ zero safe
  intro n p hn run
  have along := C.good_along tr hist (frames := pre ++ mid) (rest := post) split
    ((entryAsks T pre).length + n) p (by
      rw [entryAsks_append, List.length_append]
      omega)
  apply along
  rw [entryAsks_append, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, Book.run_append, atPre, Option.bind_some]
  exact run

end Blanc.Lift.Token
