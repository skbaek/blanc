import Blanc.SlotFootprint
import Blanc.Lift.MapSlot
import Blanc.Lift.UniswapV2Pair.Layout

/-! Finite tracked Pair storage, without universal hashed-map correspondence. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive WriterKey
  | balance (owner : Adr)
  | allowance (owner spender : Adr)
  | nonce (owner : Adr)
  deriving DecidableEq

def WriterKey.slot : WriterKey → B256
  | .balance a => mapSlot a.toB256 1
  | .allowance o p => mapSlot p.toB256 (mapSlot o.toB256 2)
  | .nonce a => mapSlot a.toB256 4

def WriterKey.value (st : State) : WriterKey → B256
  | .balance a => st.balanceOf a
  | .allowance o p => st.allowance o p
  | .nonce a => st.nonces a

def writerFixedSlots : List B256 := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def WriterKeysFinite (K : WriterKey → Prop) : Prop :=
  ∃ keys : List WriterKey, ∀ k, K k ↔ k ∈ keys

abbrev WriterSupport (K : WriterKey → Prop) (s : Stor) : Prop :=
  Blanc.SlotFootprint.Support WriterKey.slot writerFixedSlots K s
abbrev WriterInj (K : WriterKey → Prop) : Prop :=
  Blanc.SlotFootprint.Inj WriterKey.slot K
abbrev WriterApart (K : WriterKey → Prop) : Prop :=
  Blanc.SlotFootprint.Apart WriterKey.slot writerFixedSlots K
abbrev WriterFreshKeys (K : WriterKey → Prop) (keys : List WriterKey) : Prop :=
  Blanc.SlotFootprint.FreshKeys WriterKey.slot writerFixedSlots K keys
abbrev WriterExtend (K : WriterKey → Prop) (keys : List WriterKey) : WriterKey → Prop :=
  Blanc.SlotFootprint.extendBy K keys

def WriterSelectedValues (K : WriterKey → Prop) (s : Stor) (st : State) : Prop :=
  ∀ k, K k → s.get k.slot = k.value st

/-- Untracked logical rows are zero; their possibly colliding raw hashes are unconstrained. -/
def WriterLogicalZero (K : WriterKey → Prop) (st : State) : Prop :=
  ∀ k, ¬ K k → k.value st = 0

def WriterFixedMatches (s : Stor) (st : State) : Prop :=
  s.get 0 = st.totalSupply ∧ s.get 3 = st.domainSeparator ∧
  (s.get 5).toAdr = st.factory ∧ (s.get 6).toAdr = st.token0 ∧
  (s.get 7).toAdr = st.token1 ∧
  reserve0Read (s.get 8) = Nat.toB256 st.reserve0.val ∧
  reserve1Read (s.get 8) = Nat.toB256 st.reserve1.val ∧
  reserveTimestampRead (s.get 8) = st.blockTimestampLast.toB256 ∧
  s.get 9 = st.price0CumulativeLast ∧ s.get 10 = st.price1CumulativeLast ∧
  s.get 11 = st.kLast ∧ s.get 12 = st.unlocked

structure WriterRep (K : WriterKey → Prop) (s : Stor) (st : State) : Prop where
  finite : WriterKeysFinite K
  fixed : WriterFixedMatches s st
  support : WriterSupport K s
  inj : WriterInj K
  apart : WriterApart K
  selected : WriterSelectedValues K s st
  logicalZero : WriterLogicalZero K st

def approveTouched (owner spender : Adr) : List WriterKey := [.allowance owner spender]

def approveSourceState (st : State) (owner spender : Adr) (amount : B256) : State :=
  { st with allowance := (Function.update st.allowance owner
      (Function.update (st.allowance owner) spender amount)) }


theorem WriterRep.get_fresh {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) {k : WriterKey}
    (fresh : Blanc.SlotFootprint.Fresh WriterKey.slot writerFixedSlots K k) :
    s.get k.slot = k.value st := by
  by_cases tracked : K k
  · exact rep.selected k tracked
  · rw [rep.logicalZero k tracked]
    exact rep.support.get_eq_zero fresh tracked

theorem WriterRep.extend {K : WriterKey → Prop} {s : Stor} {st : State}
    {keys : List WriterKey} (rep : WriterRep K s st)
    (fresh : WriterFreshKeys K keys) : WriterRep (WriterExtend K keys) s st := by
  rcases rep.finite with ⟨old, finite⟩
  refine ⟨⟨old ++ keys, ?_⟩, rep.fixed, rep.support.mono (fun _ h => .inl h),
    rep.inj.extend fresh, rep.apart.extend fresh, ?_, ?_⟩
  · intro k
    change (K k ∨ k ∈ keys) ↔ k ∈ old ++ keys
    rw [List.mem_append, ← finite k]
  · intro k tracked
    rcases tracked with old | touched
    · exact rep.selected k old
    · exact rep.get_fresh (fresh.1 k touched)
  · intro k outside
    exact rep.logicalZero k (fun tracked => outside (.inl tracked))

theorem WriterRep.balance_zero_outside {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) {a : Adr} (outside : ¬ K (.balance a)) :
    st.balanceOf a = 0 := rep.logicalZero (.balance a) outside


theorem approveSourceState_value (st : State) (owner spender : Adr) (amount : B256)
    (k : WriterKey) :
    k.value (approveSourceState st owner spender amount) =
      if k = .allowance owner spender then amount else k.value st := by
  cases k with
  | balance a => rfl
  | nonce a => rfl
  | allowance a p =>
    dsimp only [WriterKey.value, approveSourceState]
    by_cases sameOwner : a = owner
    · subst a
      by_cases sameSpender : p = spender
      · subst p
        rw [ite_eq_left rfl, Function.update_self, Function.update_self]
      · have different : WriterKey.allowance owner p ≠ .allowance owner spender :=
          fun eq => sameSpender (WriterKey.allowance.inj eq).2
        rw [ite_eq_right different, Function.update_self, Function.update_of_ne sameSpender]
    · have different : WriterKey.allowance a p ≠ .allowance owner spender :=
        fun eq => sameOwner (WriterKey.allowance.inj eq).1
      rw [ite_eq_right different, Function.update_of_ne sameOwner]


theorem WriterRep.approve_store {K : WriterKey → Prop} {s : Stor} {st : State}
    {owner spender : Adr} {amount : B256} (rep : WriterRep K s st)
    (fresh : WriterFreshKeys K (approveTouched owner spender)) :
    WriterRep (WriterExtend K (approveTouched owner spender))
      (s.set (WriterKey.slot (.allowance owner spender)) amount)
      (approveSourceState st owner spender amount) := by
  have extended := rep.extend fresh
  have touched : WriterExtend K (approveTouched owner spender) (.allowance owner spender) :=
    .inr (List.mem_singleton.mpr rfl)
  have off := extended.apart (.allowance owner spender) touched
  have unchanged (n : B256) (fixed : n ∈ writerFixedSlots) :
      (s.set (WriterKey.slot (.allowance owner spender)) amount).get n = s.get n :=
    Stor.get_set_ne s (k := WriterKey.slot (.allowance owner spender)) (a := n)
      (fun eq => off (eq.symm ▸ fixed)) amount
  refine ⟨extended.finite, ?_, extended.support.set touched amount,
    extended.inj, extended.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches, approveSourceState]
    rw [unchanged 0 (by decide), unchanged 3 (by decide), unchanged 5 (by decide),
      unchanged 6 (by decide), unchanged 7 (by decide), unchanged 8 (by decide),
      unchanged 9 (by decide), unchanged 10 (by decide), unchanged 11 (by decide),
      unchanged 12 (by decide)]
    exact rep.fixed
  · intro k tracked
    by_cases same : k = .allowance owner spender
    · subst k
      rw [Stor.get_set_self, approveSourceState_value, ite_eq_left rfl]
    · have separate : WriterKey.slot (.allowance owner spender) ≠ k.slot :=
        fun eq => same (extended.inj k (.allowance owner spender) tracked touched eq.symm)
      rw [Stor.get_set_ne s separate amount, approveSourceState_value, ite_eq_right same]
      exact extended.selected k tracked
  · intro k outside
    have different : k ≠ .allowance owner spender := by
      intro eq
      subst k
      exact outside touched
    rw [approveSourceState_value, ite_eq_right different]
    exact extended.logicalZero k outside

end Blanc.Lift.UniswapV2Pair
