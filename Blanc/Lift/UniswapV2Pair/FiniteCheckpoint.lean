import Blanc.Lift.FiniteCheckpoint
import Blanc.Lift.UniswapV2Pair.WriterStorage

/-!
# The Pair's storage representation by a finite checker

A finite Pair checkpoint is a base model state (its fixed fields: supply, reserves, tokens, lock and
the rest) and a row list of mapping keys, each with its precomputed slot word and its value.  The
model state the rows describe, `rowsState base rows`, reads each listed key's value and zero at
every unlisted key, so `WriterLogicalZero` holds by construction.  `checkPair rows s base` decides
`WriterRep (pairKeys rows) s (rowsState base rows)`: the contract-neutral footprint checker over
the rows' words (complete support over the storage tree), each listed slot holding its value, and
the fixed slots matching the base state (`checkPair_sound`).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.Lift.FiniteCheckpoint

/-- A tracked Pair row: a mapping key, its slot word and its value. -/
abbrev PairRow := WriterKey × B256 × B256

/-- The key-and-word part of the rows. -/
def slotRows (rows : List PairRow) : List (WriterKey × B256) := rows.map fun r => (r.1, r.2.1)

/-- The tracked keys: the listed keys. -/
def pairKeys (rows : List PairRow) : WriterKey → Prop := rowKeys (slotRows rows)

theorem slotRows_keys (rows : List PairRow) :
    (slotRows rows).map Prod.fst = rows.map Prod.fst := by
  simp only [slotRows, List.map_map]
  rfl

/-- The value the rows give a key: the first listed value, zero when unlisted. -/
def rowValue : List PairRow → WriterKey → B256
  | [], _ => 0
  | r :: rows, k => if r.1 = k then r.2.2 else rowValue rows k

theorem rowValue_of_not_mem {k : WriterKey} :
    ∀ {rows : List PairRow}, k ∉ rows.map Prod.fst → rowValue rows k = 0
  | [], _ => rfl
  | r :: rows, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : r.1 ≠ k := fun he => h.1 he.symm
    simp only [rowValue, hne, ↓reduceIte]
    exact rowValue_of_not_mem h.2

theorem rowValue_of_mem :
    ∀ {rows : List PairRow}, (rows.map Prod.fst).Nodup → ∀ r ∈ rows, rowValue rows r.1 = r.2.2
  | [], _, _, hr => absurd hr List.not_mem_nil
  | r₀ :: rows, h, r, hr => by
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [rowValue, ↓reduceIte]
    · have hne : r₀.1 ≠ r.1 := fun he => h.1 (he ▸ List.mem_map_of_mem hr)
      simp only [rowValue, hne, ↓reduceIte]
      exact rowValue_of_mem h.2 r hr

/-- The model state the rows describe over a base state's fixed fields. -/
def rowsState (base : State) (rows : List PairRow) : State :=
  { base with
    balanceOf := fun a => rowValue rows (.balance a)
    allowance := fun o p => rowValue rows (.allowance o p)
    nonces := fun a => rowValue rows (.nonce a) }

theorem rowsState_value (base : State) (rows : List PairRow) (k : WriterKey) :
    k.value (rowsState base rows) = rowValue rows k := by
  cases k <;> rfl

instance (s : Stor) (st : State) : Decidable (WriterFixedMatches s st) :=
  inferInstanceAs (Decidable (s.get 0 = st.totalSupply ∧ s.get 3 = st.domainSeparator ∧
    (s.get 5).toAdr = st.factory ∧ (s.get 6).toAdr = st.token0 ∧
    (s.get 7).toAdr = st.token1 ∧
    reserve0Read (s.get 8) = Nat.toB256 st.reserve0.val ∧
    reserve1Read (s.get 8) = Nat.toB256 st.reserve1.val ∧
    reserveTimestampRead (s.get 8) = st.blockTimestampLast.toB256 ∧
    s.get 9 = st.price0CumulativeLast ∧ s.get 10 = st.price1CumulativeLast ∧
    s.get 11 = st.kLast ∧ s.get 12 = st.unlocked))

/-- **The Pair checker**: the footprint over the rows' words, each listed slot holding its listed
value, and the fixed slots matching the base state. -/
def checkPair (rows : List PairRow) (s : Stor) (base : State) : Bool :=
  checkRows WriterKey.slot writerFixedSlots (slotRows rows) s &&
    rows.all (fun r => decide (s.get r.2.1 = r.2.2)) && decide (WriterFixedMatches s base)

/-- **Soundness of the Pair checker.** -/
theorem checkPair_sound {rows : List PairRow} {s : Stor} {base : State}
    (h : checkPair rows s base = true) :
    WriterRep (pairKeys rows) s (rowsState base rows) := by
  simp only [checkPair, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hrows, hvals⟩, hfixed⟩ := h
  have sound := checkRows_sound hrows
  have nodup : (rows.map Prod.fst).Nodup := slotRows_keys rows ▸ sound.nodup
  refine ⟨⟨(slotRows rows).map Prod.fst, fun _ => Iff.rfl⟩, hfixed, sound.support, sound.inj,
    sound.apart, ?_, ?_⟩
  · intro k hk
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    have hword : WriterKey.slot r.1 = r.2.1 := sound.word _ (List.mem_map_of_mem hr)
    change s.get (WriterKey.slot r.1) = r.1.value (rowsState base rows)
    rw [hword, rowsState_value, rowValue_of_mem nodup r hr]
    exact hvals r hr
  · intro k hk
    rw [rowsState_value]
    apply rowValue_of_not_mem
    change k ∉ (slotRows rows).map Prod.fst at hk
    rw [slotRows_keys] at hk
    exact hk

end Blanc.Lift.UniswapV2Pair
