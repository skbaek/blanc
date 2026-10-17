import Blanc.Lift.Token.Holder
import Blanc.Lift.Token.HolderLaws
import Blanc.Lift.Token.SelfCaller

/-!
# Token interface core: the writer-shadowed core (Route R)

`CoreW` is `Core` with the positional replay law required only at settled frames that are not
`Shadowed`, plus the two shadow laws the generic walk needs.  `Core.weak` (nothing shadowed) and
`SelfCaller.weak` keep every `Core` instance a `CoreW` one.  Over a `CoreW` and the holder-indexed
laws: every ledger along a settled prefix's replay is good (`CoreW.good_along`), and the holder
segment (`CoreW.run_holder_segment`).  Contract-neutral.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

/-- **The writer-shadowed token core.**  As `Core`, except that the positional replay law is
required only at settled frames that are not `Shadowed`: frames inside a writer entry before its
effect lands (a proxy's delegatecalled implementation frame, and what that frame runs before its
storage writes).  `Core.replayAt` is unsatisfiable for any proxy token with a nontrivial writer: the
implementation frame starts in its entry frame's state but after its entry ask in pre-order.  The
shadow laws are what the generic walk needs: a shadowed frame is static or a non-entry frame at `T`
(`shadow_kind`), and an unshadowed frame elsewhere has unshadowed children (`child_unshadowed`). -/
structure CoreW (T : Adr) (B : Book) where
  Hist : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain},
    ConfiguredHistoryTrace cfg checkpoint future → Prop
  ledgerOf : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain},
    ConfiguredHistoryTrace cfg checkpoint future → State → B.Ledger
  Answerable : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain},
    ConfiguredHistoryTrace cfg checkpoint future → Adr → Prop
  Shadowed : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain},
    ConfiguredHistoryTrace cfg checkpoint future → Exec.Frame → Prop
  shadow_kind : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ f ∈ tr.settledFrames, Shadowed tr f →
        f.sevm.isStatic = true ∨ (f.sevm.currentTarget = T ∧ ¬ IsEntry T f)
  child_unshadowed : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ P ∈ tr.settledFrames, P.sevm.currentTarget ≠ T → ¬ Shadowed tr P →
        ∀ c ∈ Exec.childFrames P.run, ¬ Shadowed tr c
  replayAt : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      tr.settledFrames = before ++ f :: after → ¬ Shadowed tr f →
      B.run (ledgerOf tr checkpoint.state) (entryAsks T before) = some (ledgerOf tr f.pre.state)
  replayEnd : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      B.run (ledgerOf tr checkpoint.state) (entryAsks T tr.settledFrames) =
        some (ledgerOf tr future.state)
  goodStart : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      B.Good (ledgerOf tr checkpoint.state)
  goodAt : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ f ∈ tr.settledFrames, B.Good (ledgerOf tr f.pre.state)
  balanceAnswer : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ g ∈ tr.settledFrames, IsEntry T g → ∀ {h : Adr}, B.op g.sevm = .balanceOf h →
        Answerable tr h →
        g.post.output = (Nat.toB256 (B.bal (ledgerOf tr g.pre.state) h)).toBytes
  transferAnswer : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ g ∈ tr.settledFrames, IsEntry T g → ∀ {dst : Adr} {v : Nat},
        B.op g.sevm = .transfer dst v →
        g.post.output = [] ∨ (32 ≤ g.post.output.length ∧
          Bytes.toB256 (g.post.output.sliceD 0 32 0) ≠ 0)
  decodes : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), Hist tr →
      ∀ g ∈ tr.settledFrames, g.sevm.currentTarget = T → ¬ IsEntry T g →
        ∀ P ∈ tr.settledFrames, g ∈ Exec.childFrames P.run → P.sevm.currentTarget = T

/-- Every `Core` is a `CoreW` with nothing shadowed (same `Hist`, `ledgerOf`, `Answerable`). -/
def Core.weak {T : Adr} {B : Book} (C : Core T B) : CoreW T B where
  Hist := C.Hist
  ledgerOf := C.ledgerOf
  Answerable := C.Answerable
  Shadowed _ _ := False
  shadow_kind _ _ _ _ h := h.elim
  child_unshadowed _ _ _ _ _ _ _ _ h := h
  replayAt tr hist before f after split _ := C.replayAt tr hist before f after split
  replayEnd := C.replayEnd
  goodStart := C.goodStart
  goodAt := C.goodAt
  balanceAnswer := C.balanceAnswer
  transferAnswer := C.transferAnswer
  decodes := C.decodes

/-- `SelfCaller` over a `CoreW` (same field). -/
structure SelfCallerW {T : Adr} {B : Book} (C : CoreW T B) : Prop where
  child_caller : ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future), C.Hist tr →
      ∀ G ∈ tr.settledFrames, G.sevm.currentTarget = T → G.sevm.isStatic = false →
        ∀ c ∈ Exec.childFrames G.run, IsEntry T c → c.sevm.caller = T

theorem SelfCaller.weak {T : Adr} {B : Book} {C : Core T B} (self : SelfCaller C) :
    SelfCallerW C.weak :=
  ⟨self.child_caller⟩

open Classical in
/-- Every proper prefix of a list's entry messages is the entry messages of a prefix ending just
before one of the list's non-static entries (the frame whose message comes next). -/
theorem entryAsks_take_entry (T : Adr) :
    ∀ (frames : List Exec.Frame) (n : Nat), n < (entryAsks T frames).length →
      ∃ (b1 : List Exec.Frame) (g : Exec.Frame) (b2 : List Exec.Frame),
        frames = b1 ++ g :: b2 ∧ (IsEntry T g ∧ g.sevm.isStatic = false) ∧
          entryAsks T b1 = (entryAsks T frames).take n
  | [], n, h => by
    simp only [entryAsks, List.filter_nil, List.map_nil, List.length_nil] at h
    omega
  | x :: xs, n, h => by
    by_cases hx : IsEntry T x ∧ x.sevm.isStatic = false
    · have cons : ∀ ys, entryAsks T (x :: ys) = x.sevm :: entryAsks T ys := fun ys => by
        simp only [entryAsks, List.filter_cons, decide_eq_true hx, ite_true, List.map_cons]
      rw [cons] at h ⊢
      cases n with
      | zero => exact ⟨[], x, xs, rfl, hx, rfl⟩
      | succ n =>
        rw [List.length_cons] at h
        obtain ⟨b1, g, b2, eq, eg, asks⟩ := entryAsks_take_entry T xs n (by omega)
        refine ⟨x :: b1, g, b2, by rw [eq, List.cons_append], eg, ?_⟩
        rw [cons, asks, List.take_succ_cons]
    · have cons : ∀ ys, entryAsks T (x :: ys) = entryAsks T ys := fun ys => by
        simp only [entryAsks, List.filter_cons, decide_eq_false hx, Bool.false_eq_true, ite_false]
      rw [cons] at h ⊢
      obtain ⟨b1, g, b2, eq, eg, asks⟩ := entryAsks_take_entry T xs n h
      exact ⟨x :: b1, g, b2, by rw [eq, List.cons_append], eg, by rw [cons, asks]⟩

/-- `Core.good_along` for a `CoreW` (replaces it; the walk is its only consumer). -/
theorem CoreW.good_along {T : Adr} {B : Book} (C : CoreW T B) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : C.Hist tr) {frames rest : List Exec.Frame} (split : tr.settledFrames = frames ++ rest) :
    ∀ n p, n < (entryAsks T frames).length →
      B.run (C.ledgerOf tr checkpoint.state) ((entryAsks T frames).take n) = some p → B.Good p := by
  intro n p h run
  obtain ⟨b1, g, b2, eq, ⟨entry, static⟩, asks⟩ := entryAsks_take_entry T frames n h
  have settled : tr.settledFrames = b1 ++ g :: (b2 ++ rest) := by
    rw [split, eq, List.append_assoc, List.cons_append]
  have mem : g ∈ tr.settledFrames := by
    rw [settled]
    exact List.mem_append_right _ List.mem_cons_self
  have lit : ¬ C.Shadowed tr g := fun shadowed => by
    rcases C.shadow_kind tr hist g mem shadowed with st | ⟨_, notEntry⟩
    · rw [static] at st
      cases st
    · exact notEntry entry
  have at_g := C.replayAt tr hist b1 g (b2 ++ rest) settled lit
  rw [asks, run] at at_g
  cases Option.some.inj at_g
  exact C.goodAt tr hist g mem

/-- `Core.run_holder_segment` over a `CoreW` and the holder-indexed laws (replaces it). -/
theorem CoreW.run_holder_segment {T : Adr} {B : Book} (C : CoreW T B)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) (hist : C.Hist tr) {h : Adr}
    (laws : HolderLaws T B tr h)
    {pre mid post : List Exec.Frame} (split : tr.settledFrames = pre ++ mid ++ post)
    {l l' : B.Ledger} (atPre : B.run (C.ledgerOf tr checkpoint.state) (entryAsks T pre) = some l)
    (step : B.run l (entryAsks T mid) = some l') (zero : ∀ g, B.allow l h g = 0)
    (safe : ∀ a ∈ entryAsks T mid, a.caller = h → (B.op a).HolderSafe) :
    B.bal l h ≤ B.bal l' h + (((entryAsks T mid).filter fun a => decide (a.caller = h)).map
      fun a => (B.op a).debit h).sum ∧ ∀ g, B.allow l' h g = 0 := by
  refine AskLaws.run_holder step ?_ ?_ zero safe
  · intro a member
    obtain ⟨F, inMid, entry, static, rfl⟩ := mem_entryAsks member
    exact laws.ask F (by rw [split]; exact List.mem_append_left _ (List.mem_append_right _ inMid))
      entry static
  · intro n p hn run
    apply C.good_along tr hist (frames := pre ++ mid) (rest := post) split
      ((entryAsks T pre).length + n) p (by
        rw [entryAsks_append, List.length_append]
        omega)
    rw [entryAsks_append, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left, Book.run_append, atPre, Option.bind_some]
    exact run

end Blanc.Lift.Token
