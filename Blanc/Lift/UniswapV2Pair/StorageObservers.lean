import Blanc.Lift.UniswapV2Pair.PropertiesLedger
import Blanc.Lift.UniswapV2Pair.PropertiesMinLiquidity

/-!
# Pair storage observers

Short readings of the Pair's own storage words, for headlines that state their conclusion over
storage rather than over a represented model state:

* `pairReserve0`, `pairReserve1`: the two reserves packed in slot `8`;
* `lpHolders keys`: the owners of the balance rows a key list names;
* `LpLedgerBalanced keys s`: the supply word (slot `0`) is the sum of those holders' balance words;
* `MinLiquidity s`: the supply word is zero or address zero's balance word is at least `1000`.

The bridges `WriterRep.reserve0`, `WriterRep.lpLedgerBalanced` and `WriterRep.minLiquidity` read
them back from a represented model state; the support argument (an untracked balance row reads zero)
is where the history's touched keys enter.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Reserve 0 as stored in the Pair's packed slot `8`. -/
def pairReserve0 (s : Stor) : Nat := (reserve0Read (s.get 8)).toNat

/-- Reserve 1 as stored in the Pair's packed slot `8`. -/
def pairReserve1 (s : Stor) : Nat := (reserve1Read (s.get 8)).toNat

/-- The owners of the balance rows named by `keys`. -/
def lpHolders (keys : List WriterKey) : Finset Adr :=
  (keys.filterMap fun
    | .balance a => some a
    | _ => none).toFinset

/-- **The stored LP ledger balances**: the supply word is the sum of the balance words of every
holder `keys` names. -/
def LpLedgerBalanced (keys : List WriterKey) (s : Stor) : Prop :=
  (s.get 0).toNat = ledgerSumOn (lpHolders keys) fun a => s.get (WriterKey.balance a).slot

/-- **The stored minimum liquidity**: the supply word is zero, or address zero's balance word
holds at least `MINIMUM_LIQUIDITY`. -/
def MinLiquidity (s : Stor) : Prop :=
  (s.get 0).toNat = 0 ∨ 1000 ≤ (s.get (WriterKey.balance 0).slot).toNat

theorem mem_lpHolders {keys : List WriterKey} {a : Adr} :
    a ∈ lpHolders keys ↔ WriterKey.balance a ∈ keys := by
  unfold lpHolders
  rw [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨k, member, eq⟩
    cases k with
    | balance b => cases eq; exact member
    | allowance _ _ => cases eq
    | nonce _ => cases eq
  · intro member
    exact ⟨_, member, rfl⟩

private theorem reserveRead_toNat {r : Fin (2 ^ 112)} {w : B256}
    (read : w = Nat.toB256 r.val) : w.toNat = r.val := by
  rw [read]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_trans r.isLt (Nat.pow_lt_pow_right (by decide) (by decide)))

theorem WriterRep.reserve0 {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) : pairReserve0 s = st.reserve0.val :=
  reserveRead_toNat rep.fixed.2.2.2.2.2.1

theorem WriterRep.reserve1 {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) : pairReserve1 s = st.reserve1.val :=
  reserveRead_toNat rep.fixed.2.2.2.2.2.2.1

/-- A representation whose tracked keys lie in `keys`, fresh among themselves, reads every
touched row's model value, and the model is zero off `keys`. -/
private theorem WriterRep.touched {K : WriterKey → Prop} {s : Stor} {st : State}
    {keys : List WriterKey} (rep : WriterRep K s st) (sub : ∀ k, K k → k ∈ keys)
    (fresh : WriterFreshKeys (fun _ => False) keys) :
    (∀ k ∈ keys, s.get k.slot = k.value st) ∧ ∀ k, k ∉ keys → k.value st = 0 := by
  have inj : WriterInj (WriterExtend (fun _ => False) keys) :=
    Blanc.SlotFootprint.Inj.extend (fun _ _ h => h.elim) fresh
  have apart : WriterApart (WriterExtend (fun _ => False) keys) :=
    Blanc.SlotFootprint.Apart.extend (fun _ h => h.elim) fresh
  have fresh' : WriterFreshKeys K keys :=
    Blanc.SlotFootprint.FreshKeys.of_universe inj apart (fun k h => .inr (sub k h))
      (fun k h => .inr h)
  have extended := rep.extend fresh'
  refine ⟨fun k member => extended.selected k (.inr member), fun k outside => ?_⟩
  exact rep.logicalZero k (fun tracked => outside (sub k tracked))

/-- **The LP ledger read over storage.**  A represented model state satisfying `State.Ledger`,
whose tracked keys lie in a fresh key list, has its supply word equal to the sum of the stored
balance words of the list's holders. -/
theorem WriterRep.lpLedgerBalanced {K : WriterKey → Prop} {s : Stor} {st : State}
    {keys : List WriterKey} (rep : WriterRep K s st) (sub : ∀ k, K k → k ∈ keys)
    (fresh : WriterFreshKeys (fun _ => False) keys) (ledger : st.Ledger) :
    LpLedgerBalanced keys s := by
  obtain ⟨reads, zero⟩ := rep.touched sub fresh
  unfold LpLedgerBalanced
  rw [rep.fixed.1, ← ledger.sum_eq,
    sum_eq_ledgerSumOn (coalition := lpHolders keys) (fun a nonzero => by
      rw [mem_lpHolders]
      by_contra outside
      exact nonzero (zero (.balance a) outside))]
  apply ledgerSumOn_congr
  intro a member
  exact (reads (.balance a) (mem_lpHolders.mp member)).symm

/-- **The minimum liquidity read over storage.** -/
theorem WriterRep.minLiquidity {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) (floor : st.SupplyFloor) : MinLiquidity s := by
  unfold MinLiquidity
  rw [rep.fixed.1]
  rcases floor.1 with zero | locked
  · exact .inl zero
  · right
    have tracked : K (.balance 0) := by
      by_contra untracked
      have value := rep.logicalZero (.balance 0) untracked
      change st.balanceOf 0 = 0 at value
      unfold State.MinimumLocked at locked
      rw [value, B256.toNat_zero] at locked
      exact absurd locked (by decide)
    rw [rep.selected _ tracked]
    exact locked

end Blanc.Lift.UniswapV2Pair
