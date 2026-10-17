import Blanc.Lift.Curve3Pool.Model
import Blanc.CommonProofs

/-!
# The deployed 3pool storage layout, its abstraction, and the checkpoint predicate

Vyper 0.2.4 lays `StableSwap3Pool.vy`'s storage out as (U0 report §1.6, confirmed on chain;
the constructor's bytes write exactly these slots, `Creation/Walk.lean`):

* `coins[i]` at `keccak(0) + i` and `balances[i]` at `keccak(1) + i` (`i < 3`). The two digests
  are concrete words: `coinsBase` and `balancesBase` below, each pinned to its Keccak-256 preimage
  by a kernel evaluation (`coinsBase_eq`, `balancesBase_eq`), so no statement about these slots
  carries a hash premise;
* the scalars at slots 2–16 in the source's declaration order (`fee` … `kill_deadline`);
* the `@nonreentrant('lock')` flag at slot `0xffffff` (U0 §5), not model state.

These 22 slots are pairwise distinct (`poolSlots_nodup`, a kernel fact).

## The abstraction (`Abstracts`)

`Abstracts stor s` relates an account's storage to a model `State`, field by field: each word
field reads its slot as a natural number (`(stor.get x).toNat`), and `is_killed` reads `1` or `0`
exactly. It is exact on the pool's slots: a storage abstracts at most one state
(`Abstracts.unique`), and two storages abstracting one state agree on every pool slot. Every word
field is below `2 ^ 256` because it is a `toNat`; this is the model's "storage words are
`< 2^256`" convention.

**Every other slot is unconstrained.** The pool has no mappings: the runtime's storage accesses
are the 21 model slots (index-checked to `i < 3` before `keccak(·) + i` is formed) and the lock
slot. No other slot can influence or be influenced by a frame, so a premise about them would add
a preservation obligation to the history theorem and narrow the states it applies to, while
buying nothing. The deployed storage does have every other slot zero, and `Creation/Deploy.lean`
proves that as part of the exact storage equation; it is not part of the checkpoint.

## The checkpoint predicate (`Checkpoint`)

What U2's history theorem starts from, at a committed boundary:

* `abs`: the storage abstracts the model state;
* `unlocked`: the lock slot reads `0`. The five guarded functions (`add_liquidity`, `exchange`,
  the three withdrawals) revert on entry unless it is `0`, set it to `1`, and clear it before
  `STOP`; a revert rolls it back. Without this conjunct a guarded frame need not refine
  `Model.step`, whose guarded functions do not fail on the lock;
* `addr`: the five address-typed fields (`owner`, the three coins, `token`) and `future_owner` are
  below `2 ^ 160`, the model's address convention (`Model.lean`, "Conventions"). The runtime does
  not re-clamp a stored address; the bound makes the stored word the `toB256` of the address the
  frame calls (`coins[i]`, `token`) and compares with `msg.sender` (`owner`), and it is preserved
  because every write of these slots stores a clamped argument (`commit_transfer_ownership`) or
  copies one (`apply_transfer_ownership`).

Nothing else: the model is total over `Nat` with checked arithmetic, so no further word bound is
assumed at entry.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-! ## Slots -/

/-- `keccak(0)`: the base of `coins`. -/
def coinsBase : B256 := 0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563

/-- `keccak(1)`: the base of `balances`. -/
def balancesBase : B256 := 0xb10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6

/-- `coinsBase` is the Keccak-256 digest of the word `0` (kernel evaluation). -/
theorem coinsBase_eq : Bytes.keccak (0 : B256).toBytes = coinsBase := by decide +kernel

/-- `balancesBase` is the Keccak-256 digest of the word `1` (kernel evaluation). -/
theorem balancesBase_eq : Bytes.keccak (1 : B256).toBytes = balancesBase := by decide +kernel

/-- `coins[i]`. -/
def coinSlot (i : Fin 3) : B256 := coinsBase + Nat.toB256 i.val

/-- `balances[i]`. -/
def balanceSlot (i : Fin 3) : B256 := balancesBase + Nat.toB256 i.val

def feeSlot : B256 := 2
def adminFeeSlot : B256 := 3
def ownerSlot : B256 := 4
def tokenSlot : B256 := 5
def initialASlot : B256 := 6
def futureASlot : B256 := 7
def initialATimeSlot : B256 := 8
def futureATimeSlot : B256 := 9
def adminActionsDeadlineSlot : B256 := 10
def transferOwnershipDeadlineSlot : B256 := 11
def futureFeeSlot : B256 := 12
def futureAdminFeeSlot : B256 := 13
def futureOwnerSlot : B256 := 14
def isKilledSlot : B256 := 15
def killDeadlineSlot : B256 := 16

/-- The `@nonreentrant('lock')` flag. -/
def lockSlot : B256 := 0xffffff

/-- Every slot the pool's code uses: the 21 model slots and the lock. -/
def poolSlots : List B256 :=
  [coinSlot 0, coinSlot 1, coinSlot 2, balanceSlot 0, balanceSlot 1, balanceSlot 2,
    feeSlot, adminFeeSlot, ownerSlot, tokenSlot, initialASlot, futureASlot, initialATimeSlot,
    futureATimeSlot, adminActionsDeadlineSlot, transferOwnershipDeadlineSlot, futureFeeSlot,
    futureAdminFeeSlot, futureOwnerSlot, isKilledSlot, killDeadlineSlot, lockSlot]

/-- The pool's slots are pairwise distinct (kernel evaluation of the two digests' offsets). -/
theorem poolSlots_nodup : poolSlots.Nodup := by decide +kernel

/-! ## The storage abstraction -/

/-- The stored word of `is_killed`. -/
def boolWord (b : Bool) : B256 := if b then 1 else 0

/-- **The storage abstraction**: every model field reads its slot (see the module note). -/
structure Abstracts (stor : Stor) (s : State) : Prop where
  coins : ∀ i : Fin 3, (stor.get (coinSlot i)).toNat = s.coins.get i
  balances : ∀ i : Fin 3, (stor.get (balanceSlot i)).toNat = s.balances.get i
  fee : (stor.get feeSlot).toNat = s.fee
  adminFee : (stor.get adminFeeSlot).toNat = s.adminFee
  owner : (stor.get ownerSlot).toNat = s.owner
  token : (stor.get tokenSlot).toNat = s.token
  initialA : (stor.get initialASlot).toNat = s.initialA
  futureA : (stor.get futureASlot).toNat = s.futureA
  initialATime : (stor.get initialATimeSlot).toNat = s.initialATime
  futureATime : (stor.get futureATimeSlot).toNat = s.futureATime
  adminActionsDeadline : (stor.get adminActionsDeadlineSlot).toNat = s.adminActionsDeadline
  transferOwnershipDeadline :
    (stor.get transferOwnershipDeadlineSlot).toNat = s.transferOwnershipDeadline
  futureFee : (stor.get futureFeeSlot).toNat = s.futureFee
  futureAdminFee : (stor.get futureAdminFeeSlot).toNat = s.futureAdminFee
  futureOwner : (stor.get futureOwnerSlot).toNat = s.futureOwner
  isKilled : stor.get isKilledSlot = boolWord s.isKilled
  killDeadline : (stor.get killDeadlineSlot).toNat = s.killDeadline

/-- The address-typed fields are addresses. -/
def State.AddrBounded (s : State) : Prop :=
  s.owner < 2 ^ 160 ∧ s.coins.v0 < 2 ^ 160 ∧ s.coins.v1 < 2 ^ 160 ∧ s.coins.v2 < 2 ^ 160 ∧
    s.token < 2 ^ 160 ∧ s.futureOwner < 2 ^ 160

/-- **U2's checkpoint predicate** (see the module note): the storage abstracts `s`, the lock is
clear, and the address fields are addresses. -/
structure Checkpoint (stor : Stor) (s : State) : Prop where
  abs : Abstracts stor s
  unlocked : stor.get lockSlot = 0
  addr : s.AddrBounded

theorem boolWord_inj {a b : Bool} (h : boolWord a = boolWord b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem V3.ext_get {v w : V3} (h : ∀ i : Fin 3, v.get i = w.get i) : v = w := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  cases v
  cases w
  simp only [V3.get, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
    one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at h0 h1 h2
  rw [h0, h1, h2]

/-- **Exactness, model side**: a storage abstracts at most one state. -/
theorem Abstracts.unique {stor : Stor} {s t : State} (hs : Abstracts stor s)
    (ht : Abstracts stor t) : s = t := by
  have hc : s.coins = t.coins := V3.ext_get fun i => (hs.coins i).symm.trans (ht.coins i)
  have hb : s.balances = t.balances :=
    V3.ext_get fun i => (hs.balances i).symm.trans (ht.balances i)
  have hk : s.isKilled = t.isKilled := boolWord_inj (hs.isKilled.symm.trans ht.isKilled)
  have e1 := hs.fee.symm.trans ht.fee
  have e2 := hs.adminFee.symm.trans ht.adminFee
  have e3 := hs.owner.symm.trans ht.owner
  have e4 := hs.token.symm.trans ht.token
  have e5 := hs.initialA.symm.trans ht.initialA
  have e6 := hs.futureA.symm.trans ht.futureA
  have e7 := hs.initialATime.symm.trans ht.initialATime
  have e8 := hs.futureATime.symm.trans ht.futureATime
  have e9 := hs.adminActionsDeadline.symm.trans ht.adminActionsDeadline
  have e10 := hs.transferOwnershipDeadline.symm.trans ht.transferOwnershipDeadline
  have e11 := hs.futureFee.symm.trans ht.futureFee
  have e12 := hs.futureAdminFee.symm.trans ht.futureAdminFee
  have e13 := hs.futureOwner.symm.trans ht.futureOwner
  have e14 := hs.killDeadline.symm.trans ht.killDeadline
  cases s
  cases t
  simp only [State.mk.injEq]
  exact ⟨hc, hb, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, hk, e14⟩

/-- **Exactness, storage side**: two storages abstracting one state agree on every model slot. -/
theorem Abstracts.agree {stor stor' : Stor} {s : State} (h : Abstracts stor s)
    (h' : Abstracts stor' s) : ∀ x ∈ poolSlots, x ≠ lockSlot → stor.get x = stor'.get x := by
  intro x hx hl
  have e : ∀ {w w' : B256} {n : Nat}, w.toNat = n → w'.toNat = n → w = w' :=
    fun h1 h2 => B256.toNat_inj _ _ (h1.trans h2.symm)
  simp only [poolSlots, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e (h.coins 0) (h'.coins 0)
  · exact e (h.coins 1) (h'.coins 1)
  · exact e (h.coins 2) (h'.coins 2)
  · exact e (h.balances 0) (h'.balances 0)
  · exact e (h.balances 1) (h'.balances 1)
  · exact e (h.balances 2) (h'.balances 2)
  · exact e h.fee h'.fee
  · exact e h.adminFee h'.adminFee
  · exact e h.owner h'.owner
  · exact e h.token h'.token
  · exact e h.initialA h'.initialA
  · exact e h.futureA h'.futureA
  · exact e h.initialATime h'.initialATime
  · exact e h.futureATime h'.futureATime
  · exact e h.adminActionsDeadline h'.adminActionsDeadline
  · exact e h.transferOwnershipDeadline h'.transferOwnershipDeadline
  · exact e h.futureFee h'.futureFee
  · exact e h.futureAdminFee h'.futureAdminFee
  · exact e h.futureOwner h'.futureOwner
  · exact h.isKilled.trans h'.isKilled.symm
  · exact e h.killDeadline h'.killDeadline
  · exact absurd rfl hl

end Blanc.Lift.Curve3Pool
