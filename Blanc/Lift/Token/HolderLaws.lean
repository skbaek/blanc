import Blanc.Lift.Token.Core

/-!
# Token interface core: holder-indexed laws (Route R)

The per-message laws of one holder (`AskLaws`), the segment form of the holder argument over them
(`AskLaws.run_holder`), and the trace-local holder-indexed law structure the generic walk consumes
(`HolderLaws`), with the bridge from the universal `BookLaws`.  Contract-neutral; no storage layout.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

/-- **The laws of one entered message for one holder** (Route R): the four per-step fields of
`BookLaws` that `BookLaws.run_holder` consumes, for a fixed holder `h` and a fixed message `a`. -/
structure AskLaws (B : Book) (h : Adr) (a : Sevm) : Prop where
  holder_only : ∀ {l l' : B.Ledger}, B.Good l → B.step l a = some l' →
    B.bal l' h < B.bal l h → a.caller = h ∨ 0 < B.allow l h a.caller
  allow_owner : ∀ {l l' : B.Ledger} {g : Adr}, B.Good l → B.step l a = some l' →
    B.allow l h g < B.allow l' h g → a.caller = h
  holder_debit : ∀ {l l' : B.Ledger}, B.Good l → B.step l a = some l' →
    a.caller = h → (B.op a).HolderSafe → B.bal l h ≤ B.bal l' h + (B.op a).debit h
  allow_safe : ∀ {l l' : B.Ledger} {g : Adr}, B.Good l → B.step l a = some l' →
    a.caller = h → (B.op a).HolderSafe → B.allow l' h g ≤ B.allow l h g

theorem BookLaws.askLaws {B : Book} (laws : BookLaws B) (h : Adr) (a : Sevm) : AskLaws B h a :=
  ⟨laws.holder_only, laws.allow_owner, laws.holder_debit, laws.allow_safe⟩

/-- **Segment form of the holder argument over per-message laws** (the body of
`BookLaws.run_holder` moves here; `BookLaws.run_holder` becomes
`AskLaws.run_holder (fun a _ => laws.askLaws h a)`, statement verbatim). -/
theorem AskLaws.run_holder {B : Book} {h : Adr} :
    ∀ {as : List Sevm} {l l' : B.Ledger},
      B.run l as = some l' →
      (∀ a ∈ as, AskLaws B h a) →
      (∀ n pre, n < as.length → B.run l (as.take n) = some pre → B.Good pre) →
      (∀ g, B.allow l h g = 0) →
      (∀ a ∈ as, a.caller = h → (B.op a).HolderSafe) →
      B.bal l h ≤ B.bal l' h + ((as.filter fun a => decide (a.caller = h)).map
        fun a => (B.op a).debit h).sum ∧
      ∀ g, B.allow l' h g = 0 := by
  intro as
  induction as with
  | nil =>
    intro l l' hrun _ _ hz _
    simp only [Book.run, Option.some.injEq] at hrun
    subst hrun
    exact ⟨Nat.le_add_right _ _, hz⟩
  | cons a as ih =>
    intro l l' hrun hlaws hgood hz hsafe
    have la : AskLaws B h a := hlaws a List.mem_cons_self
    simp only [Book.run] at hrun
    cases hs : B.step l a with
    | none => rw [hs, Option.bind_none] at hrun; cases hrun
    | some m =>
      rw [hs, Option.bind_some] at hrun
      have gl : B.Good l := hgood 0 l (Nat.zero_lt_succ _) rfl
      have hzm : ∀ g, B.allow m h g = 0 := by
        intro g
        by_cases hc : a.caller = h
        · have := la.allow_safe (g := g) gl hs hc (hsafe a List.mem_cons_self hc)
          rw [hz g] at this
          exact Nat.le_zero.mp this
        · have hle : B.allow m h g ≤ B.allow l h g :=
            Nat.not_lt.mp fun hlt => hc (la.allow_owner gl hs hlt)
          rw [hz g] at hle
          exact Nat.le_zero.mp hle
      obtain ⟨ihb, iha⟩ := ih hrun (fun a' ha' => hlaws a' (List.mem_cons_of_mem a ha'))
        (fun n pre hn hpre => hgood (n + 1) pre (Nat.succ_lt_succ hn)
          (by simp only [List.take_succ_cons, Book.run, hs, Option.bind_some]; exact hpre))
        hzm (fun a' ha' => hsafe a' (List.mem_cons_of_mem a ha'))
      refine ⟨?_, iha⟩
      by_cases hc : a.caller = h
      · have hd := la.holder_debit gl hs hc (hsafe a List.mem_cons_self hc)
        simp only [List.filter_cons, hc, decide_true, ite_true, List.map_cons, List.sum_cons]
        omega
      · have hle : B.bal l h ≤ B.bal m h := Nat.not_lt.mp fun hlt => by
          rcases la.holder_only gl hs hlt with h1 | h1
          · exact hc h1
          · rw [hz] at h1; exact Nat.lt_irrefl 0 h1
        simp only [List.filter_cons, hc, decide_false, Bool.false_eq_true, ite_false]
        omega

/-- **The holder-indexed law structure the generic walk consumes** (Route R).  Trace-local: the
per-message laws hold for `h` at every settled non-static entry of `T` in `tr`, and good ledgers
book `h` below `2 ^ 256`. -/
structure HolderLaws (T : Adr) (B : Book) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) (h : Adr) : Prop where
  ask : ∀ g ∈ tr.settledFrames, IsEntry T g → g.sevm.isStatic = false → AskLaws B h g.sevm
  bal_lt : ∀ {l : B.Ledger}, B.Good l → B.bal l h < 2 ^ 256

/-- Bridge 1: the universal laws give the holder-indexed laws for every holder on every trace. -/
theorem BookLaws.holderLaws {B : Book} (laws : BookLaws B) (T : Adr) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (h : Adr) : HolderLaws T B tr h :=
  ⟨fun g _ _ _ => laws.askLaws h g.sevm, laws.bal_lt⟩

open Classical in
/-- A message among the entry messages of a list is the message of one of its non-static
entries.  (Hoisted from `Blanc/Composition/PairTokenCallers.lean`.) -/
theorem mem_entryAsks {T : Adr} {frames : List Exec.Frame} {a : Sevm}
    (member : a ∈ entryAsks T frames) :
    ∃ F ∈ frames, IsEntry T F ∧ F.sevm.isStatic = false ∧ F.sevm = a := by
  obtain ⟨F, inFilter, rfl⟩ := List.mem_map.mp member
  obtain ⟨inFrames, picked⟩ := List.mem_filter.mp inFilter
  obtain ⟨entry, static⟩ := of_decide_eq_true picked
  exact ⟨F, inFrames, entry, static, rfl⟩

end Blanc.Lift.Token
