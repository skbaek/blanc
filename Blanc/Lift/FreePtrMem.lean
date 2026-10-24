import Blanc.Lift.FreePtrFacts
import Blanc.Lift.MemPotential
import Blanc.Lift.StepMemory

/-!
# Soundness of the free-pointer checker's memory effect (`memEff`, unit F3b)

Goal `usdc-neversigner-freepointer-v1`, design `fp-checker.md` §1 points 3–5. Contract-neutral.
`fpRun_sound` (F3c) cites these at every step `fstep` accepts, without reopening `memEff`:

* `memEff_fpWord`: the symbol `memEff` returns names the free-pointer word after the step
  (`FpWord`): the store of a good value at constant `64` names the stored symbol; a write whose
  window `apartW` places outside `[64, 96)` keeps `fp` (every writer: `MSTORE`, `MSTORE8`,
  `CALLDATACOPY`, `CODECOPY`, `RETURNDATACOPY`, and the output windows of `CALL`, `DELEGATECALL`,
  `STATICCALL`); every other instruction the transfer accepts leaves the word alone.  `MCOPY`,
  `EXTCODECOPY`, `CALLCODE` and `CREATE` are rejected by `ninstTransfer`, hence by `fstep`.
* `memEff_touched`: the potential facts `memEff` adds hold after the step, under `Pot d'`
  (`Pot.size_lt`): the executed window ends inside the new memory size, which is below `memCap`.
* `memEff_obs`, `memEff_mload_top`: the strict read sees a good pointer, and the free-pointer
  `MLOAD` pushes the pointer symbol's value.

Fact meaning is F3a's (`Fact.Holds`, `AllHold`, `lo_le`/`le_hi`, `apartW_sound`, …).  Memory is
indexed by `Nat` in Jaune, so a missed window (`Miss64`) is a plain `Nat` inequality: no write can
wrap around `2^256` onto the word.  The per-instruction memory shapes are in
`Blanc/Lift/StepMemory.lean`.
-/

namespace Blanc.Lift.FreePtr

open Jaune AbstractStackSafety

/-! ## The free-pointer word -/

/-- The checker's free-pointer symbol `fp` names the word `memWord μ 64`: when it is known,
the memory covers `[64, 96)`, the word there is the symbol's value, and that value is good
(`fpLo ≤ · ≤ fpCap`). -/
def FpWord (ν : Nat → B256) (fp : Option Nat) (μ : Mem) : Prop :=
  ∀ s, fp = some s →
    96 ≤ μ.size ∧ memWord μ 64 = ν s ∧ fpLo ≤ (ν s).toNat ∧ (ν s).toNat ≤ fpCap

theorem FpWord.none (ν : Nat → B256) (μ : Mem) : FpWord ν none μ := fun _ h => by cases h

/-- Same bytes, no smaller: the word survives. -/
theorem FpWord.of_data {ν : Nat → B256} {fp : Option Nat} {μ μ' : Mem}
    (hd : μ'.data = μ.data) (hsz : μ.size ≤ μ'.size) (h : FpWord ν fp μ) : FpWord ν fp μ' := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := h s hs
  refine ⟨le_trans h1 hsz, ?_, h3⟩
  rw [← h2]
  unfold memWord Mem.read
  rw [hd]

theorem FpWord.extends {ν : Nat → B256} {fp : Option Nat} {μ : Mem} (ps : List (Nat × Nat))
    (h : FpWord ν fp μ) : FpWord ν fp (μ.extends ps) :=
  FpWord.of_data (μ := μ) rfl (Blanc.Lift.memExtsSize_ge _ _) h

/-- A byte window `[o, o + n)` misses the free-pointer word `[64, 96)`.  Jaune indexes memory by
`Nat` (`Mem.write o ys` writes the indices `o, …, o + ys.length - 1`), so a window never wraps
around `2^256` onto the word. -/
def Miss64 (o n : Nat) : Prop := n = 0 ∨ o + n ≤ 64 ∨ 96 ≤ o

/-- **A write that misses the free-pointer word keeps it** (on any memory covering it). -/
theorem memWord64_write {μ : Mem} {o : Nat} {ys : Bytes} (hsz : 96 ≤ μ.size)
    (miss : Miss64 o ys.length) :
    96 ≤ (μ.write o ys).size ∧ memWord (μ.write o ys) 64 = memWord μ 64 := by
  have hag := Mem.write_agree μ o ys
  refine ⟨le_trans hsz hag.1, memWord_congr fun j hj => hag.2 _ (by omega) ?_⟩
  unfold Miss64 at miss
  omega

theorem FpWord.write {ν : Nat → B256} {fp : Option Nat} {μ : Mem} {o : Nat} {ys : Bytes}
    (miss : Miss64 o ys.length) (h : FpWord ν fp μ) : FpWord ν fp (μ.write o ys) := by
  intro s hs
  obtain ⟨h1, h2, h3⟩ := h s hs
  obtain ⟨k1, k2⟩ := memWord64_write h1 miss
  exact ⟨k1, k2.trans h2, h3⟩

/-- The free-pointer store: a good value written at `64` becomes the word. -/
theorem FpWord.store {ν : Nat → B256} {μ : Mem} {v : Nat}
    (hg : fpLo ≤ (ν v).toNat ∧ (ν v).toNat ≤ fpCap) :
    FpWord ν (some v) (μ.write 64 (ν v).toBytes) := by
  intro s hs
  cases hs
  obtain ⟨hw, hsz⟩ := Mem.memWord_write_word μ 64 (ν v)
  exact ⟨hsz, hw, hg⟩

/-- The checker's window test, read semantically: a write of at most `(ν l).toNat` bytes at
`ν a` accepted by `hi fs l = 0 || apartW fs a (hi fs l)` misses the word. -/
theorem miss_of_apartW {ν : Nat → B256} {fs : List Fact} (hf : AllHold ν fs) {a l n : Nat}
    (h : (hi fs l = 0 || apartW fs a (hi fs l)) = true) (hn : n ≤ (ν l).toNat) :
    Miss64 (ν a).toNat n := by
  have hl := le_hi hf l
  rcases Bool.or_eq_true_iff.mp h with h0 | ha
  · left
    have : hi fs l = 0 := of_decide_eq_true h0
    omega
  · have := apartW_sound hf ha (Nat.le_trans hn hl)
    unfold Miss64
    omega

theorem memEff_keeps_fp {fs : List Fact} {fp fp' : Option Nat} {r : Rinst} {kv : List Nat}
    {gas : List Fact} (hk : rinstMemKeeps r = true)
    (he : memEff fs fp (.reg r) kv = some (fp', gas)) : fp' = fp := by
  cases r <;> simp only [rinstMemKeeps, Bool.false_eq_true] at hk
  case mload =>
    rcases kv with _ | ⟨a, kv⟩
    · simp only [memEff, reduceCtorEq] at he
    · simp only [memEff] at he
      split at he
      · exact (Prod.mk.inj (Option.some.inj he)).1.symm
      · split at he
        · split at he
          · exact (Prod.mk.inj (Option.some.inj he)).1.symm
          · cases he
        · cases he
  all_goals simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he; exact he.1.symm

/-- `memEff`'s free-pointer verdict on a step that keeps the pointer word. -/
private theorem fp_keep {fs : List Fact} {fp fp' : Option Nat} {n : Ninst} {kv : List Nat}
    {gas : List Fact} (he : memEff fs fp n kv = some (fp', gas))
    (hc : memEff fs fp n kv = some (fp, [])) : fp' = fp :=
  (Prod.mk.inj (Option.some.inj (he.symm.trans hc))).1

/-- **Soundness of `memEff`'s free-pointer verdict.**  If the step's input symbols `kv` name the
top stack words `S` (under the valuation `ν` that satisfies `fs`), the transfer accepted the step,
and `fp` named the pointer word before it, then the symbol `memEff` returns names it after: the
free-pointer store of a good value names the stored symbol, a write whose window provably misses
`[64, 96)` keeps `fp`, and every other accepted instruction leaves the word alone.  The missing
windows are `Nat` windows (`Miss64`): Jaune's memory never wraps. -/
theorem memEff_fpWord_noStateGas {ν : Nat → B256} {fs : List Fact} {fp fp' : Option Nat} {n : Ninst}
    {kv : List Nat} {gas : List Fact} {out : Pattern} {S rest : List B256} {sevm : Sevm}
    {d d' : Devm} (hsg : sevm.benvStat.rules.stateGas = none)
    (ht : ninstTransfer n (indexPattern kv.length) = some out)
    (he : memEff fs fp n kv = some (fp', gas)) (hf : AllHold ν fs)
    (hS : List.Forall₂ (fun s w => ν s = w) kv S) (hstack : d.stack = S ++ rest)
    (hw : FpWord ν fp d.memory) (run : Ninst.Run sevm d n d') :
    FpWord ν fp' d'.memory := by
  cases n with
  | push bs h => cases ht
  | dupn i => cases ht
  | swapn i => cases ht
  | exchange i => cases ht
  | exec x =>
    cases x with
    | create => cases ht
    | callcode => cases ht
    | create2 =>
      rcases kv with _ | ⟨e, _ | ⟨mi, _ | ⟨ms, _ | ⟨sa, kv⟩⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      rw [fp_keep he rfl]
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩⟩
      rw [run_create2_memory_noStateGas hsg hstack run]
      exact hw.extends _
    | call =>
      rcases kv with _ | ⟨g, _ | ⟨c, _ | ⟨v, _ | ⟨ii, _ | ⟨is, _ | ⟨o, _ | ⟨l, kv⟩⟩⟩⟩⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩⟩⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_call_memory_noStateGas hsg hstack run
      rw [hm]
      split
      · exact (hw.extends _).write (miss_of_apartW hf ‹_› hl)
      · exact FpWord.none _ _
    | delegatecall =>
      rcases kv with _ | ⟨g, _ | ⟨c, _ | ⟨ii, _ | ⟨is, _ | ⟨o, _ | ⟨l, kv⟩⟩⟩⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_delegatecall_memory_noStateGas hsg hstack run
      rw [hm]
      split
      · exact (hw.extends _).write (miss_of_apartW hf ‹_› hl)
      · exact FpWord.none _ _
    | staticcall =>
      rcases kv with _ | ⟨g, _ | ⟨c, _ | ⟨ii, _ | ⟨is, _ | ⟨o, _ | ⟨l, kv⟩⟩⟩⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_staticcall_memory_noStateGas hsg hstack run
      rw [hm]
      split
      · exact (hw.extends _).write (miss_of_apartW hf ‹_› hl)
      · exact FpWord.none _ _
  | reg r =>
    by_cases hk : rinstMemKeeps r = true
    · obtain ⟨hd, hsz⟩ := ninstMemKeeps_run (n := .reg r) hk run
      rw [memEff_keeps_fp hk he]
      exact FpWord.of_data hd hsz hw
    cases r <;> simp only [rinstMemKeeps, not_true_eq_false] at hk
    all_goals try (cases ht; done)
    case exp =>
      rw [fp_keep he rfl, run_exp_memory run]
      exact hw
    case balance =>
      rw [fp_keep he rfl, run_balance_memory run]
      exact hw
    case extcodesize =>
      rw [fp_keep he rfl, run_extcodesize_memory run]
      exact hw
    case extcodehash =>
      rw [fp_keep he rfl, run_extcodehash_memory run]
      exact hw
    case selfbalance =>
      rw [fp_keep he rfl, run_selfbalance_memory run]
      exact hw
    case mstore =>
      rcases kv with _ | ⟨a, _ | ⟨v, kv⟩⟩
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩
      rw [mstore_run_memory run hstack]
      simp only [memEff] at he
      split at he
      · rename_i hc
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj he)
        rw [constOf_sound hf hc]
        split
        · exact FpWord.store (good_sound hf ‹_›)
        · exact FpWord.none _ _
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj he)
        split
        · have := apartW_sound hf ‹_› (Nat.le_refl 32)
          refine hw.write ?_
          rw [B256.length_toBytes]
          unfold Miss64
          omega
        · exact FpWord.none _ _
    case mstore8 =>
      rcases kv with _ | ⟨a, _ | ⟨v, kv⟩⟩
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_mstore8_memory hstack run
      rw [hm]
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      split
      · have := apartW_sound hf ‹_› (Nat.le_refl 1)
        refine hw.write ?_
        rw [hl]
        unfold Miss64
        omega
      · exact FpWord.none _ _
    case calldatacopy =>
      rcases kv with _ | ⟨o, _ | ⟨src, _ | ⟨l, kv⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := calldatacopy_run_memory run hstack
      rw [hm]
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      split
      · exact hw.write (miss_of_apartW hf ‹_› hl.le)
      · exact FpWord.none _ _
    case codecopy =>
      rcases kv with _ | ⟨o, _ | ⟨src, _ | ⟨l, kv⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_codecopy_memory hstack run
      rw [hm]
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      split
      · exact hw.write (miss_of_apartW hf ‹_› hl.le)
      · exact FpWord.none _ _
    case returndatacopy =>
      rcases kv with _ | ⟨o, _ | ⟨src, _ | ⟨l, kv⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_returndatacopy_memory hstack run
      rw [hm]
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      split
      · exact hw.write (miss_of_apartW hf ‹_› hl.le)
      · exact FpWord.none _ _

/-- Covered-fork projection of free-pointer memory-effect soundness. -/
theorem memEff_fpWord {ν : Nat → B256} {fs : List Fact} {fp fp' : Option Nat} {n : Ninst}
    {kv : List Nat} {gas : List Fact} {out : Pattern} {S rest : List B256} {sevm : Sevm}
    {d d' : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (ht : ninstTransfer n (indexPattern kv.length) = some out)
    (he : memEff fs fp n kv = some (fp', gas)) (hf : AllHold ν fs)
    (hS : List.Forall₂ (fun s w => ν s = w) kv S) (hstack : d.stack = S ++ rest)
    (hw : FpWord ν fp d.memory) (run : Ninst.Run sevm d n d') :
    FpWord ν fp' d'.memory :=
  memEff_fpWord_noStateGas hfork.rules_stateGas_none ht he hf hS hstack hw run

/-! ## Touched windows are bounded -/

/-- **The `touched` facts hold** once the window `[ν a, ν a + len)` ends below `memCap`: every
symbol `t` the facts bound is `a` itself or below it by an `le` fact. -/
theorem touched_holds {ν : Nat → B256} {fs : List Fact} {a len : Nat} (hf : AllHold ν fs)
    (hend : (ν a).toNat + len ≤ memCap) : AllHold ν (touched fs a len) := by
  intro f hfm
  simp only [touched, List.mem_map, List.mem_cons, List.mem_filterMap] at hfm
  obtain ⟨t, ht, rfl⟩ := hfm
  have hta : (ν t).toNat ≤ (ν a).toNat := by
    rcases ht with rfl | ⟨g, hg, hgt⟩
    · exact Nat.le_refl _
    · cases g with
      | le t' a' =>
        dsimp only at hgt
        split at hgt
        · rename_i ha
          cases hgt
          subst ha
          exact hf _ hg
        · cases hgt
      | _ => cases hgt
  exact ⟨Nat.zero_le _, by omega⟩

private theorem gas_nil {ν : Nat → B256} {fs : List Fact} {fp fp' x : Option Nat} {n : Ninst}
    {kv : List Nat} {gas : List Fact} (he : memEff fs fp n kv = some (fp', gas))
    (hc : memEff fs fp n kv = some (x, [])) : AllHold ν gas := by
  rw [(Prod.mk.inj (Option.some.inj (he.symm.trans hc))).2]
  exact fun _ h => nomatch h

theorem memEff_touched {ν : Nat → B256} {fs : List Fact} {fp fp' : Option Nat} {n : Ninst}
    {kv : List Nat} {gas : List Fact} {out : Pattern} {S rest : List B256} {sevm : Sevm}
    {d d' : Devm} (ht : ninstTransfer n (indexPattern kv.length) = some out)
    (he : memEff fs fp n kv = some (fp', gas)) (hf : AllHold ν fs)
    (hS : List.Forall₂ (fun s w => ν s = w) kv S) (hstack : d.stack = S ++ rest)
    (run : Ninst.Run sevm d n d') (pot : Pot d') : AllHold ν gas := by
  have hcap := pot.size_lt
  cases n with
  | push bs h => cases ht
  | dupn i => cases ht
  | swapn i => cases ht
  | exchange i => cases ht
  | exec x =>
    cases x with
    | create => cases ht
    | callcode => cases ht
    | create2 => exact gas_nil he rfl
    | call =>
      rcases kv with _ | ⟨g, _ | ⟨c, _ | ⟨v, _ | ⟨ii, _ | ⟨is, _ | ⟨o, _ | ⟨l, kv⟩⟩⟩⟩⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      exact gas_nil he rfl
    | delegatecall =>
      rcases kv with _ | ⟨g, _ | ⟨c, _ | ⟨ii, _ | ⟨is, _ | ⟨o, _ | ⟨l, kv⟩⟩⟩⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      exact gas_nil he rfl
    | staticcall =>
      rcases kv with _ | ⟨g, _ | ⟨c, _ | ⟨ii, _ | ⟨is, _ | ⟨o, _ | ⟨l, kv⟩⟩⟩⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      · cases ht
      exact gas_nil he rfl
  | reg r =>
    cases r
    all_goals try (cases ht; done)
    all_goals try (exact gas_nil he rfl)
    case mload =>
      rcases kv with _ | ⟨a, kv⟩
      · cases ht
      rcases hS with _ | ⟨rfl, hS⟩
      have hsz : (ν a).toNat + 32 ≤ d'.memory.size := by
        rw [run_mload_memory hstack run]
        exact Jaune.memExtSize_access_le _ _ _ (by decide)
      have hT := touched_holds (len := 32) hf (a := a) (by omega)
      simp only [memEff] at he
      split at he
      · rw [← (Prod.mk.inj (Option.some.inj he)).2]
        exact hT
      · split at he
        · split at he
          · rw [← (Prod.mk.inj (Option.some.inj he)).2]
            exact hT
          · cases he
        · cases he
    case mstore =>
      rcases kv with _ | ⟨a, _ | ⟨v, kv⟩⟩
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩
      have hsz : (ν a).toNat + 32 ≤ d'.memory.size := by
        rw [mstore_run_memory run hstack]
        exact (Mem.memWord_write_word _ _ _).2
      have hT := touched_holds (len := 32) hf (a := a) (by omega)
      simp only [memEff] at he
      split at he
      all_goals
        rw [← (Prod.mk.inj (Option.some.inj he)).2]
        exact hT
    case mstore8 =>
      rcases kv with _ | ⟨a, _ | ⟨v, kv⟩⟩
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_mstore8_memory hstack run
      have hne : ys ≠ [] := by
        rintro rfl
        cases hl
      have hsz := Mem.write_size_ge d.memory (ν a).toNat hne
      rw [← hm, hl] at hsz
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.2]
      exact touched_holds hf (by omega)
    case calldatacopy =>
      rcases kv with _ | ⟨o, _ | ⟨src, _ | ⟨l, kv⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := calldatacopy_run_memory run hstack
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.2]
      split
      · rename_i h1
        have hlo := lo_le hf l
        have hne : ys ≠ [] := by
          rintro rfl
          simp only [List.length_nil] at hl
          omega
        have hsz := Mem.write_size_ge d.memory (ν o).toNat hne
        rw [← hm] at hsz
        exact touched_holds hf (by omega)
      · exact fun _ h => nomatch h
    case codecopy =>
      rcases kv with _ | ⟨o, _ | ⟨src, _ | ⟨l, kv⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_codecopy_memory hstack run
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.2]
      split
      · rename_i h1
        have hlo := lo_le hf l
        have hne : ys ≠ [] := by
          rintro rfl
          simp only [List.length_nil] at hl
          omega
        have hsz := Mem.write_size_ge d.memory (ν o).toNat hne
        rw [← hm] at hsz
        exact touched_holds hf (by omega)
      · exact fun _ h => nomatch h
    case returndatacopy =>
      rcases kv with _ | ⟨o, _ | ⟨src, _ | ⟨l, kv⟩⟩⟩
      · cases ht
      · cases ht
      · cases ht
      rcases hS with _ | ⟨rfl, _ | ⟨rfl, _ | ⟨rfl, hS⟩⟩⟩
      obtain ⟨ys, hl, hm⟩ := run_returndatacopy_memory hstack run
      simp only [memEff, Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.2]
      split
      · rename_i h1
        have hlo := lo_le hf l
        have hne : ys ≠ [] := by
          rintro rfl
          simp only [List.length_nil] at hl
          omega
        have hsz := Mem.write_size_ge d.memory (ν o).toNat hne
        rw [← hm] at hsz
        exact touched_holds hf (by omega)
      · exact fun _ h => nomatch h


/-! ## The free-pointer read -/

/-- **The strict read is sound**: an `MLOAD` that `memEff` accepts and whose operand is `64`
reads a good free pointer (the frozen observation `FpObs`, unfolded). -/
theorem memEff_obs {ν : Nat → B256} {fs : List Fact} {fp fp' : Option Nat} {kv : List Nat}
    {gas : List Fact} {S rest : List B256} {d : Devm}
    (he : memEff fs fp (.reg .mload) kv = some (fp', gas)) (hf : AllHold ν fs)
    (hS : List.Forall₂ (fun s w => ν s = w) kv S) (hstack : d.stack = S ++ rest)
    (hw : FpWord ν fp d.memory) (h64 : d.stack.head? = some 64) :
    fpLo ≤ (memWord d.memory 64).toNat ∧ (memWord d.memory 64).toNat ≤ fpCap := by
  rcases kv with _ | ⟨a, kv⟩
  · cases he
  rcases hS with _ | ⟨rfl, hS⟩
  rw [hstack] at h64
  have ha : ν a = 64 := Option.some.inj h64
  simp only [memEff] at he
  split at he
  · rename_i hn
    exact absurd (by rw [ha]; rfl) (not64_sound hf hn)
  · split at he
    · rename_i s
      obtain ⟨-, h2, h3⟩ := hw s rfl
      rw [h2]
      exact h3
    · cases he

/-- **The free-pointer read names the pointer's symbol**: an accepted `MLOAD` at a symbol whose
constant is `64` leaves the free-pointer symbol unchanged and known, and pushes its value
(the `r'` of `fstep`). -/
theorem memEff_mload_top {ν : Nat → B256} {fs : List Fact} {fp fp' : Option Nat} {a : Nat}
    {kv : List Nat} {gas : List Fact} {rest : List B256} {sevm : Sevm} {d d' : Devm}
    (hc : constOf fs a = some 64) (he : memEff fs fp (.reg .mload) (a :: kv) = some (fp', gas))
    (hf : AllHold ν fs) (hstack : d.stack = ν a :: rest) (hw : FpWord ν fp d.memory)
    (run : Ninst.Run sevm d (.reg .mload) d') : ∃ s, fp' = some s ∧ d'.stack = ν s :: rest := by
  have ha := constOf_sound hf hc
  rw [mload_run_stack run hstack, ha]
  simp only [memEff] at he
  split at he
  · rename_i hn
    exact absurd ha (not64_sound hf hn)
  · split at he
    · rename_i s
      split at he
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj he)
        exact ⟨s, rfl, by rw [(hw s rfl).2.1]⟩
      · cases he
    · cases he

end Blanc.Lift.FreePtr
