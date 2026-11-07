import Blanc.Lift.BuilderRequest.Deposit.Delivery

/-!
# The deposit sequence's premises can be met

`prefork_witness` builds a chain of real frames from the deployed storage: any number of submissions under a covered
fork, each the `Exec` of the code classified by `exec_user_frame`, followed by any number of empty-calldata system
calls under Amsterdam. Each frame runs on a state holding the storage the last one left, which is all `Chain` asks,
so this says nothing about a chain's history.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestSystem
open Delivery
open Creation (address)

/-- A covered-fork submission's machine: all-ones calldata and the highest value. -/
def preForkSevm : Sevm where
  caller := 1
  target := some address
  currentTarget := address
  gas := 0
  value := B256.max
  data := List.replicate 184 0xff
  codeAddress := some address
  code := code
  depth := 0
  shouldTransferValue := true
  isStatic := false
  disablePrecompiles := false
  benvStat := { (default : BenvStat) with fork := .prague }
  tenvStat := default

/-- With all-ones calldata the guards admit any word fee: it is at most a seventeenth of the word. -/
theorem preFork_admitted (o : B256) : Admitted preForkSevm (o / (17 : B256)) := by
  have amount : amountGwei preForkSevm = amountMask := by decide
  have credit : creditedWei preForkSevm = (2 ^ 64 - 1) * 10 ^ 9 := by
    rw [creditedWei, amount]
    rfl
  have hfee : (o / (17 : B256)).toNat ≤ o.toNat / 17 := by
    rw [B256.toNat_div (by decide)]
    exact Nat.le_refl _
  have ho := B256.toNat_lt o
  refine ⟨?_, ?_⟩
  · rw [credit]
    decide
  · rw [credit]
    show _ ≤ B256.max.toNat
    rw [max_toNat]
    omega

/-- From any storage off the inhibitor there is a real submission frame under a covered fork. -/
theorem exists_prefork {s : Stor} (off : s.get 0 ≠ B256.max) :
    ∃ f : Frame, f.before = s ∧ (∃ h, f.event = .submission (recordOf preForkSevm h)) ∧ PreFork f := by
  have hb := holdingDevm_getStorVal address code s
  obtain ⟨i, o, run, -⟩ := WordFakeExponential.run_exists
    (storedExcess 8 preForkSevm (holdingDevm address code s)) 17 1 17 0
  have hfork : CoveredFork preForkSevm.benvStat.fork := by decide
  have hlenB : preForkSevm.data.length = 184 := List.length_replicate ..
  obtain ⟨exec⟩ := exec_submission_exact (b := holdingDevm address code s) (M := .empty) (G := gCallStipend + 1)
    (sevm := preForkSevm) rfl hfork (show (1 : Adr) ≠ systemAddress by decide) hlenB rfl (by omega) (by
      show (holdingDevm address code s).getStorVal address 0 ≠ _
      rw [hb]
      exact off) run (preFork_admitted o)
  have frame := exec_user_frame (sevm := preForkSevm) (pre := St (holdingDevm address code s) [] .empty _) rfl hfork rfl rfl Mem.wf_empty
    (by rw [hlenB]; decide) (show (1 : Adr) ≠ systemAddress by decide) exec
  cases frame with
  | submission i' o' law =>
    exact ⟨.submission preForkSevm _ _ _ i' o' (.covered hfork) rfl (by decide) law, holding_getStor address code s, ⟨law.length, rfl⟩, hfork⟩
  | feeRead i' o' empty law => cases empty

/-- From any storage there is a real empty-calldata system call frame. -/
theorem exists_system (s : Stor) : ∃ f : Frame, f.before = s ∧ f.event = .system false := by
  refine Delivery.Frame.exists_system (c := contract) (fun s => ?_) s
  obtain ⟨o, run, -⟩ := system_call_state (benv := holdingBenv address code s) rfl (holding_getCode _ _ s)
  exact ⟨_, o, run⟩

/-- `k` real empty-calldata calls chained from any storage. -/
theorem exists_calls (s : Stor) (k : Nat) :
    ∃ (calls : List Frame) (t : Stor), Chain s calls t ∧ (∀ f ∈ calls, EmptyCall f) ∧ calls.length = k := by
  induction k generalizing s with
  | zero => exact ⟨[], s, .nil s, fun _ h => absurd h List.not_mem_nil, rfl⟩
  | succ k ih =>
    obtain ⟨f, hb, he⟩ := exists_system s
    obtain ⟨calls, t, chain, hc, hl⟩ := ih f.after
    refine ⟨f :: calls, t, .cons hb chain, ?_, by simp only [List.length_cons, hl]⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact he
    · exact hc x hx

/-- `n` real covered-fork submissions chained from any represented queue off the inhibitor. -/
theorem exists_preforks (n : Nat) {s : Stor} {st : QueueState Record} (rep : Holds contract s st)
    (hne : st.excess ≠ 2 ^ 256 - 1) (slots : queueBase 6 (st.tail + n) ≤ 2 ^ 256) (count : st.count + n < 2 ^ 256) :
    ∃ (backlog : List Frame) (t : Stor), Chain s backlog t ∧ (∀ f ∈ backlog, PreFork f) ∧ backlog.length = n := by
  induction n generalizing s st with
  | zero => exact ⟨[], s, .nil s, fun _ h => absurd h List.not_mem_nil, rfl⟩
  | succ n ih =>
    have off : s.get 0 ≠ B256.max := fun h => by
      have h0 : s.get 0 = st.excess.toB256 := rep.excess
      have := congrArg B256.toNat (h0.symm.trans h)
      rw [B256.toNat_toB256_of_lt rep.excess_lt, max_toNat] at this
      exact hne this
    obtain ⟨f, hb, ⟨_, he⟩, hp⟩ := exists_prefork off
    subst hb
    obtain ⟨hrep, -⟩ := f.step_holds rep
      (by rw [he]; exact (queueBase_mono 6 (by show st.tail + 1 ≤ _; omega)).trans slots)
      (by rw [he]; show st.count + 1 < _; omega)
    rw [he] at hrep
    obtain ⟨backlog, t, chain, hall, hl⟩ := ih hrep hne
      ((queueBase_mono 6 (by show st.tail + 1 + _ ≤ _; omega)).trans slots) (by show st.count + 1 + _ < _; omega)
    refine ⟨f :: backlog, t, .cons rfl chain, ?_, by simp only [List.length_cons, hl]⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hp
    · exact hall x hx

/-- **`prefork_then_calls`'s premises can be met**, for any `n` in word range and any `k`, by real frames from the
deployed storage. At `n = 65`, `k = 1` that corollary's queue keeps one record: a partial drain at the cap. -/
theorem prefork_witness (n k : Nat) (range : 4 + 6 * n ≤ 2 ^ 256) :
    ∃ (backlog calls : List Frame) (t : Stor), Chain Stor.empty (backlog ++ calls) t ∧
      (∀ f ∈ backlog, PreFork f) ∧ (∀ f ∈ calls, EmptyCall f) ∧ backlog.length = n ∧ calls.length = k ∧
      (submissions backlog).length = n := by
  obtain ⟨backlog, m, c1, hp, hl⟩ := exists_preforks n deployed_represents (by decide)
    (by show 4 + _ * (0 + _) ≤ _; rw [Nat.zero_add]; exact range) (by show 0 + _ < _; omega)
  obtain ⟨calls, t, c2, hc, hk⟩ := exists_calls m k
  refine ⟨backlog, calls, t, c1.append c2, hp, hc, hl, hk, ?_⟩
  rw [← hl]
  clear c1 hl
  induction backlog with
  | nil => rfl
  | cons f rest ih =>
    have hs := submitted_cons_length f.event (events rest)
    have ih' := ih (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    have hone : (submitted [f.event]).length = 1 := by
      have := hp f List.mem_cons_self
      cases f with
      | submission sevm pre post l i o rules target caller law => rfl
      | feeRead sevm pre post l i o rules target caller law => exact this.elim
      | system benv data post out fork installed length run => exact this.elim
    show (submitted (f.event :: events rest)).length = _
    rw [hs, hone, List.length_cons, Nat.add_comm]
    exact congrArg (· + 1) ih'

end Blanc.Lift.BuilderRequest.Deposit
