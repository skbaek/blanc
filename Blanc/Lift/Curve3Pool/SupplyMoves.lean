import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.U3Bounds

/-!
# The model's token moves: word amounts, one direction (pure)

A step's `mint`/`burn` calls (`Out.calls`) move 3Crv's supply.  This file states, of every
accepted step, the two facts the composed U3 statement needs to read `supplyAfter T o.calls` as an
exact ledger move:

* `MovesWord`: every `mint`/`burn` amount is a word (`< wordSize`), from the model's checked
  arithmetic (`add_liquidity`'s `chkAdd T mint`, `remove_liquidity_imbalance`'s `chkAdd burn 1`),
  from the supply being a word (`remove_liquidity`'s `chkSub T amount`), or from the call's own
  argument being a word (`remove_liquidity_one_coin`'s burned amount, a calldata word);
* `OneWay`: no step both mints and burns.

`supplyAfter_exact`: when the burns do not exceed the starting supply, `supplyAfter` is the exact
move `T + minted − burned`.
-/

namespace Blanc.Lift.Curve3Pool

open Blanc.StableSwapNewton

/-- The amounts a call list mints. -/
def mintedRaw : List ExtCall → Nat
  | [] => 0
  | .mint _ v :: cs => v + mintedRaw cs
  | _ :: cs => mintedRaw cs

/-- The amounts a call list burns. -/
def burnedRaw : List ExtCall → Nat
  | [] => 0
  | .burn _ v :: cs => v + burnedRaw cs
  | _ :: cs => burnedRaw cs

/-- Every `mint`/`burn` amount of a call list is a word. -/
def MovesWord : List ExtCall → Prop
  | [] => True
  | .mint _ v :: cs => v < wordSize ∧ MovesWord cs
  | .burn _ v :: cs => v < wordSize ∧ MovesWord cs
  | _ :: cs => MovesWord cs

/-- A call list mints nothing or burns nothing. -/
def OneWay (cs : List ExtCall) : Prop := mintedRaw cs = 0 ∨ burnedRaw cs = 0

/-- **`supplyAfter` is exact** when the burns do not exceed the starting supply. -/
theorem supplyAfter_exact : ∀ (cs : List ExtCall) (T : Nat), burnedRaw cs ≤ T →
    supplyAfter T cs + burnedRaw cs = T + mintedRaw cs
  | [], _, _ => rfl
  | .mint _ v :: cs, T, h => by
    have ih := supplyAfter_exact cs (T + v) (by simp only [burnedRaw] at h; omega)
    simp only [supplyAfter, burnedRaw, mintedRaw] at ih h ⊢
    omega
  | .burn _ v :: cs, T, h => by
    have ih := supplyAfter_exact cs (T - v) (by simp only [burnedRaw] at h; omega)
    simp only [supplyAfter, burnedRaw, mintedRaw] at ih h ⊢
    omega
  | .pull _ _ _ :: cs, T, h => by
    simp only [supplyAfter, burnedRaw, mintedRaw] at h ⊢
    exact supplyAfter_exact cs T h
  | .push _ _ _ :: cs, T, h => by
    simp only [supplyAfter, burnedRaw, mintedRaw] at h ⊢
    exact supplyAfter_exact cs T h

theorem movesWord_append : ∀ {cs ds : List ExtCall}, MovesWord cs → MovesWord ds →
    MovesWord (cs ++ ds)
  | [], _, _, h => h
  | .mint _ _ :: cs, _, h, h' => ⟨h.1, movesWord_append (cs := cs) h.2 h'⟩
  | .burn _ _ :: cs, _, h, h' => ⟨h.1, movesWord_append (cs := cs) h.2 h'⟩
  | .pull _ _ _ :: cs, _, h, h' => movesWord_append (cs := cs) h h'
  | .push _ _ _ :: cs, _, h, h' => movesWord_append (cs := cs) h h'

theorem mintedRaw_append : ∀ cs ds : List ExtCall,
    mintedRaw (cs ++ ds) = mintedRaw cs + mintedRaw ds
  | [], _ => (Nat.zero_add _).symm
  | .mint _ v :: cs, ds => by
    simp only [List.cons_append, mintedRaw, mintedRaw_append cs ds, Nat.add_assoc]
  | .burn _ _ :: cs, ds => by simp only [List.cons_append, mintedRaw, mintedRaw_append cs ds]
  | .pull _ _ _ :: cs, ds => by simp only [List.cons_append, mintedRaw, mintedRaw_append cs ds]
  | .push _ _ _ :: cs, ds => by simp only [List.cons_append, mintedRaw, mintedRaw_append cs ds]

theorem burnedRaw_append : ∀ cs ds : List ExtCall,
    burnedRaw (cs ++ ds) = burnedRaw cs + burnedRaw ds
  | [], _ => (Nat.zero_add _).symm
  | .burn _ v :: cs, ds => by
    simp only [List.cons_append, burnedRaw, burnedRaw_append cs ds, Nat.add_assoc]
  | .mint _ _ :: cs, ds => by simp only [List.cons_append, burnedRaw, burnedRaw_append cs ds]
  | .pull _ _ _ :: cs, ds => by simp only [List.cons_append, burnedRaw, burnedRaw_append cs ds]
  | .push _ _ _ :: cs, ds => by simp only [List.cons_append, burnedRaw, burnedRaw_append cs ds]

/-- The `transferFrom` calls move nothing. -/
theorem pullCalls_moves (c : Nat) (am : V3) :
    MovesWord (pullCalls c am) ∧ mintedRaw (pullCalls c am) = 0 ∧
      burnedRaw (pullCalls c am) = 0 := by
  unfold pullCalls
  simp only [List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp only [MovesWord, mintedRaw, burnedRaw, and_self]

/-- The `transfer` calls move nothing. -/
theorem pushCalls_moves (c : Nat) (am : V3) :
    MovesWord (pushCalls c am) ∧ mintedRaw (pushCalls c am) = 0 ∧
      burnedRaw (pushCalls c am) = 0 := by
  unfold pushCalls
  simp only [List.filterMap_cons, List.filterMap_nil]
  split_ifs <;> simp only [MovesWord, mintedRaw, burnedRaw, and_self]

/-- **Every accepted body's token moves are words and go one way**, when the observed supply is a
word and `remove_liquidity_one_coin`'s amount is a word. -/
theorem body_moves (s : State) (e : Env) (c : Call)
    (hT : ∀ T, e.supply = some T → T < wordSize)
    (ha : ∀ a i m, c = .removeLiquidityOneCoin a i m → a < wordSize) :
    OptAll (fun o => MovesWord o.calls ∧ OneWay o.calls) (body s e c) := by
  cases c <;> simp only [body, Curve3Pool.addLiquidity, Curve3Pool.exchange,
    Curve3Pool.removeLiquidity, Curve3Pool.removeLiquidityImbalance,
    Curve3Pool.removeLiquidityOneCoin, Curve3Pool.rampA, Curve3Pool.stopRampA,
    Curve3Pool.commitNewFee, Curve3Pool.applyNewFee, Curve3Pool.revertNewParameters,
    Curve3Pool.commitTransferOwnership, Curve3Pool.applyTransferOwnership,
    Curve3Pool.revertTransferOwnership, Curve3Pool.withdrawAdminFees,
    Curve3Pool.donateAdminFees, Curve3Pool.killMe, Curve3Pool.unkillMe] <;> opt_walk
  all_goals first
    | exact OptAll.none'
    | (apply OptAll.some'
       simp only [MovesWord, OneWay]
       exact ⟨trivial, Or.inl rfl⟩)
    | (apply OptAll.some'
       simp only [MovesWord, OneWay]
       refine ⟨movesWord_append (pullCalls_moves _ _).1
         ⟨by have := chkAdd_some_lt ‹chkAdd _ _ = some _›; omega, trivial⟩, Or.inr ?_⟩
       rw [burnedRaw_append, (pullCalls_moves _ _).2.2]
       rfl)
    | (apply OptAll.some'
       simp only [MovesWord, OneWay]
       refine ⟨⟨Nat.lt_of_le_of_lt (chkSub_some ‹chkSub _ _ = some _›).2
         (hT _ ‹e.supply = some _›), trivial⟩, Or.inl rfl⟩)
    | (apply OptAll.some'
       simp only [MovesWord, OneWay]
       exact ⟨⟨ha _ _ _ rfl, trivial⟩, Or.inl rfl⟩)
    | (apply OptAll.some'
       simp only [MovesWord, OneWay]
       exact ⟨(pushCalls_moves _ _).1, Or.inl (pushCalls_moves _ _).2.1⟩)
    | (apply OptAll.some'
       simp only [MovesWord, OneWay]
       refine ⟨⟨(chkAdd_some ‹chkAdd _ 1 = some _›) ▸ chkAdd_some_lt ‹chkAdd _ 1 = some _›,
         (pushCalls_moves _ _).1⟩, Or.inl (pushCalls_moves _ _).2.1⟩)

/-- **Every accepted step's token moves are words and go one way**, when the observed supply is a
word and `remove_liquidity_one_coin`'s amount is a word. -/
theorem step_moves {s : State} {e : Env} {c : Call} {o : Out} (h : step s e c = some o)
    (hT : ∀ T, e.supply = some T → T < wordSize)
    (ha : ∀ a i m, c = .removeLiquidityOneCoin a i m → a < wordSize) :
    MovesWord o.calls ∧ OneWay o.calls := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · exact body_moves s e _ hT ha o h
    · cases h

/-- The decoded `remove_liquidity_one_coin` amount is a calldata word. -/
theorem decodeCall_oneCoin_word {sevm : Jaune.Sevm} {a i m : Nat}
    (h : decodeCall sevm = .removeLiquidityOneCoin a i m) : a < wordSize := by
  unfold decodeCall at h
  split at h
  · cases h
  · split at h
    · unfold callAt at h
      split at h <;> cases h
      exact Jaune.B256.toNat_lt _
    · cases h

end Blanc.Lift.Curve3Pool
