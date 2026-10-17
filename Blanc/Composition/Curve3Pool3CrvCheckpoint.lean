import Blanc.Lift.Curve3Pool.Layout
import Blanc.Lift.Curve3Crv.Layout
import Blanc.Curve3Crv.Properties
import Blanc.Lift.FiniteCheckpoint
import Blanc.Lift.LedgerFootprint

/-!
# The joint checkpoint of the Curve 3pool and 3Crv, decided by a finite checker

`JointCheckpoint pool c3crv ps cs K w` is a predicate on one world state, however it
was produced: the pool's storage abstracts the model state `ps` with the lock clear
and the address fields bounded (`Lift.Curve3Pool.Checkpoint`); 3Crv's storage abstracts
the model state `cs` over the live keys `K` (`Lift.Curve3Crv.VyInv`, which carries
`Conserved`, so the supply is the sum of balances); and the cross-links hold: the
pool's `token` is the 3Crv address and 3Crv's `minter` is the pool address.

The pool keeps no mappings, so its checker `checkPool` reads the fixed slots against
`ps` directly.  3Crv's checker `checkC3` follows the finite-checker kit
(`FiniteCheckpoint.checkRows`): each row carries its key, its precomputed slot word
and its value; the model state `rowsState base rows` reads each listed key's value
and zero at every unlisted key; conservation is decided as
`supply.toNat = rowsBalSum rows` over the listed balance rows and transported to the
full address sum by `footprintSum_eq_sum`.  `checkJoint_sound` is the soundness
theorem; `world_joint` closes one concrete synthetic world (three small synthetic
coins, one 3Crv holder) by `decide` on the checker.
-/

namespace Blanc.Composition.Curve3Pool3CrvJoint

open Jaune Blanc Blanc.Lift.FiniteCheckpoint

/-! ## 3Crv rows and the model state they describe -/

/-- A tracked 3Crv row: a mapping key, its slot word and its value. -/
abbrev C3Row := Lift.Curve3Crv.Key × B256 × B256

/-- The key-and-word part of the rows. -/
def slotRows (rows : List C3Row) : List (Lift.Curve3Crv.Key × B256) :=
  rows.map fun r => (r.1, r.2.1)

/-- The tracked keys: the listed keys. -/
def c3Keys (rows : List C3Row) : Lift.Curve3Crv.Key → Prop := rowKeys (slotRows rows)

theorem slotRows_keys (rows : List C3Row) :
    (slotRows rows).map Prod.fst = rows.map Prod.fst := by
  simp only [slotRows, List.map_map]
  rfl

/-- The value the rows give a key: the first listed value, zero when unlisted. -/
def rowValue : List C3Row → Lift.Curve3Crv.Key → B256
  | [], _ => 0
  | r :: rows, k => if r.1 = k then r.2.2 else rowValue rows k

theorem rowValue_of_not_mem {k : Lift.Curve3Crv.Key} :
    ∀ {rows : List C3Row}, k ∉ rows.map Prod.fst → rowValue rows k = 0
  | [], _ => rfl
  | r :: rows, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hne : r.1 ≠ k := fun he => h.1 he.symm
    simp only [rowValue, hne, ↓reduceIte]
    exact rowValue_of_not_mem h.2

theorem rowValue_of_mem :
    ∀ {rows : List C3Row}, (rows.map Prod.fst).Nodup → ∀ r ∈ rows, rowValue rows r.1 = r.2.2
  | [], _, _, hr => absurd hr List.not_mem_nil
  | r₀ :: rows, h, r, hr => by
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [rowValue, ↓reduceIte]
    · have hne : r₀.1 ≠ r.1 := fun he => h.1 (he ▸ List.mem_map_of_mem hr)
      simp only [rowValue, hne, ↓reduceIte]
      exact rowValue_of_mem h.2 r hr

/-- The fixed (non-mapping) 3Crv fields the rows sit over. -/
structure C3Base where
  decimals : B256
  supply : B256
  minter : Adr
  name : Bytes
  symbol : Bytes

/-- The model state the rows describe over the base's fixed fields. -/
def rowsState (base : C3Base) (rows : List C3Row) : Curve3Crv.State :=
  { name := base.name
    symbol := base.symbol
    decimals := base.decimals
    balanceOf := fun a => rowValue rows (Lift.Curve3Crv.Key.bal a)
    allowances := fun o p => rowValue rows (Lift.Curve3Crv.Key.allow o p)
    totalSupply := base.supply
    minter := base.minter }

theorem rowsState_value (base : C3Base) (rows : List C3Row) (k : Lift.Curve3Crv.Key) :
    Lift.Curve3Crv.Key.val (rowsState base rows) k = rowValue rows k := by
  cases k <;> rfl

/-! ## Listed balance rows and conservation -/

/-- The listed balance rows: each holder with its slot word and value. -/
def balRows : List C3Row → List (Adr × B256 × B256)
  | [] => []
  | (.bal a, x, v) :: rows => (a, x, v) :: balRows rows
  | (.allow _ _, _, _) :: rows => balRows rows

theorem mem_balRows {a : Adr} {x v : B256} :
    ∀ {rows : List C3Row},
      (a, x, v) ∈ balRows rows ↔ (Lift.Curve3Crv.Key.bal a, x, v) ∈ rows
  | [] => by simp only [balRows, List.not_mem_nil]
  | (.bal b, y, w) :: rows => by
    simp only [balRows, List.mem_cons, Prod.mk.injEq, Lift.Curve3Crv.Key.bal.injEq,
      mem_balRows]
  | (.allow o p, y, w) :: rows => by
    simp only [balRows, List.mem_cons, Prod.mk.injEq, reduceCtorEq, false_and, false_or,
      mem_balRows]

/-- The listed holders. -/
def holders (rows : List C3Row) : List Adr := (balRows rows).map fun r => r.1

theorem holders_nodup :
    ∀ {rows : List C3Row}, (rows.map Prod.fst).Nodup → (holders rows).Nodup
  | [], _ => List.nodup_nil
  | (.bal a, x, v) :: rows, h => by
    show (((a, x, v) :: balRows rows).map fun r => r.1).Nodup
    simp only [List.map_cons, List.nodup_cons] at h ⊢
    refine ⟨fun ha => h.1 ?_, holders_nodup h.2⟩
    obtain ⟨r, hr, hra⟩ := List.mem_map.mp ha
    have hr' := mem_balRows.mp (show (a, r.2.1, r.2.2) ∈ balRows rows from hra ▸ hr)
    exact List.mem_map_of_mem (f := Prod.fst) hr'
  | (.allow _ _, _, _) :: rows, h => by
    simp only [List.map_cons, List.nodup_cons] at h
    show ((balRows rows).map fun r => r.1).Nodup
    exact holders_nodup h.2

/-- The sum of the listed balance values. -/
def rowsBalSum (rows : List C3Row) : Nat :=
  ((balRows rows).map fun r => r.2.2.toNat).sum

/-- The listed holders carry the footprint sum of the rows' balance function. -/
theorem rowsBalSum_eq_footprintSum {rows : List C3Row} {base : C3Base}
    (nodup : (rows.map Prod.fst).Nodup) :
    footprintSum (holders rows) (rowsState base rows).balanceOf = rowsBalSum rows := by
  unfold footprintSum rowsBalSum holders
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun r hr => by
    show ((rowsState base rows).balanceOf r.1).toNat = (r.2.2).toNat
    have hrow : (Lift.Curve3Crv.Key.bal r.1, r.2.1, r.2.2) ∈ rows := mem_balRows.mp hr
    have hval : rowValue rows (Lift.Curve3Crv.Key.bal r.1) = r.2.2 :=
      rowValue_of_mem nodup _ hrow
    have hbal : (rowsState base rows).balanceOf r.1 =
        rowValue rows (Lift.Curve3Crv.Key.bal r.1) := rfl
    rw [hbal, hval]))

/-- The listed holders cover every nonzero row of the rows' balance function. -/
theorem holders_covers (rows : List C3Row) (base : C3Base) :
    FootprintCovers (holders rows) (rowsState base rows).balanceOf := by
  intro a ha
  by_cases hK : Lift.Curve3Crv.Key.bal a ∈ rows.map Prod.fst
  · obtain ⟨r, hr, hrfl⟩ := List.mem_map.mp hK
    have heta : r = (r.1, r.2.1, r.2.2) := rfl
    have hrow : (Lift.Curve3Crv.Key.bal a, r.2.1, r.2.2) ∈ rows := heta ▸ hrfl ▸ hr
    exact List.mem_map_of_mem (f := fun t => t.1) (mem_balRows.mpr hrow)
  · exact absurd (rowValue_of_not_mem hK) ha

/-- Conservation of the rows' model state from the checker's supply equation. -/
theorem rowsState_conserved {rows : List C3Row} {base : C3Base}
    (nodup : (rows.map Prod.fst).Nodup)
    (hsupply : base.supply.toNat = rowsBalSum rows) :
    Curve3Crv.Conserved (rowsState base rows) := by
  unfold Curve3Crv.Conserved
  have hsup : (rowsState base rows).totalSupply = base.supply := rfl
  rw [hsup, hsupply, ← rowsBalSum_eq_footprintSum nodup,
    footprintSum_eq_sum (holders_nodup nodup) (holders_covers rows base)]

/-! ## The pool checker: fixed slots against the model state -/

/-- **The pool checker**: every model slot reads the model state, the lock is clear,
and the address fields are addresses.  The pool keeps no mappings, so no footprint
walk is needed: `Checkpoint` constrains no other slot. -/
def checkPool (stor : Stor) (ps : Lift.Curve3Pool.State) : Bool :=
  decide ((stor.get (Lift.Curve3Pool.coinSlot 0)).toNat = ps.coins.get 0) &&
  decide ((stor.get (Lift.Curve3Pool.coinSlot 1)).toNat = ps.coins.get 1) &&
  decide ((stor.get (Lift.Curve3Pool.coinSlot 2)).toNat = ps.coins.get 2) &&
  decide ((stor.get (Lift.Curve3Pool.balanceSlot 0)).toNat = ps.balances.get 0) &&
  decide ((stor.get (Lift.Curve3Pool.balanceSlot 1)).toNat = ps.balances.get 1) &&
  decide ((stor.get (Lift.Curve3Pool.balanceSlot 2)).toNat = ps.balances.get 2) &&
  decide ((stor.get Lift.Curve3Pool.feeSlot).toNat = ps.fee) &&
  decide ((stor.get Lift.Curve3Pool.adminFeeSlot).toNat = ps.adminFee) &&
  decide ((stor.get Lift.Curve3Pool.ownerSlot).toNat = ps.owner) &&
  decide ((stor.get Lift.Curve3Pool.tokenSlot).toNat = ps.token) &&
  decide ((stor.get Lift.Curve3Pool.initialASlot).toNat = ps.initialA) &&
  decide ((stor.get Lift.Curve3Pool.futureASlot).toNat = ps.futureA) &&
  decide ((stor.get Lift.Curve3Pool.initialATimeSlot).toNat = ps.initialATime) &&
  decide ((stor.get Lift.Curve3Pool.futureATimeSlot).toNat = ps.futureATime) &&
  decide ((stor.get Lift.Curve3Pool.adminActionsDeadlineSlot).toNat =
    ps.adminActionsDeadline) &&
  decide ((stor.get Lift.Curve3Pool.transferOwnershipDeadlineSlot).toNat =
    ps.transferOwnershipDeadline) &&
  decide ((stor.get Lift.Curve3Pool.futureFeeSlot).toNat = ps.futureFee) &&
  decide ((stor.get Lift.Curve3Pool.futureAdminFeeSlot).toNat = ps.futureAdminFee) &&
  decide ((stor.get Lift.Curve3Pool.futureOwnerSlot).toNat = ps.futureOwner) &&
  decide (stor.get Lift.Curve3Pool.isKilledSlot = Lift.Curve3Pool.boolWord ps.isKilled) &&
  decide ((stor.get Lift.Curve3Pool.killDeadlineSlot).toNat = ps.killDeadline) &&
  decide (stor.get Lift.Curve3Pool.lockSlot = 0) &&
  decide (ps.owner < 2 ^ 160) &&
  decide (ps.coins.get 0 < 2 ^ 160) &&
  decide (ps.coins.get 1 < 2 ^ 160) &&
  decide (ps.coins.get 2 < 2 ^ 160) &&
  decide (ps.token < 2 ^ 160) &&
  decide (ps.futureOwner < 2 ^ 160)

/-- **Soundness of the pool checker.** -/
theorem checkPool_sound {stor : Stor} {ps : Lift.Curve3Pool.State}
    (h : checkPool stor ps = true) : Lift.Curve3Pool.Checkpoint stor ps := by
  simp only [checkPool, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcoin0, hcoin1⟩, hcoin2⟩, hbal0⟩, hbal1⟩, hbal2⟩,
    hfee⟩, hadminFee⟩, howner⟩, htoken⟩, hinitA⟩, hfutA⟩, hinitAT⟩, hfutAT⟩, hdeadline⟩,
    htransfer⟩, hfutFee⟩, hfutAdminFee⟩, hfutOwner⟩, hkilled⟩, hkill⟩, hunlocked⟩,
    hownerB⟩, hcoinB0⟩, hcoinB1⟩, hcoinB2⟩, htokenB⟩, hfutOwnerB⟩ := h
  have hcoins : ∀ i : Fin 3,
      (stor.get (Lift.Curve3Pool.coinSlot i)).toNat = ps.coins.get i := by
    intro i
    match i with
    | ⟨0, _⟩ => exact hcoin0
    | ⟨1, _⟩ => exact hcoin1
    | ⟨2, _⟩ => exact hcoin2
    | ⟨n + 3, hi⟩ => exact absurd hi (by omega)
  have hbals : ∀ i : Fin 3,
      (stor.get (Lift.Curve3Pool.balanceSlot i)).toNat = ps.balances.get i := by
    intro i
    match i with
    | ⟨0, _⟩ => exact hbal0
    | ⟨1, _⟩ => exact hbal1
    | ⟨2, _⟩ => exact hbal2
    | ⟨n + 3, hi⟩ => exact absurd hi (by omega)
  exact
    { abs :=
      { coins := hcoins
        balances := hbals
        fee := hfee
        adminFee := hadminFee
        owner := howner
        token := htoken
        initialA := hinitA
        futureA := hfutA
        initialATime := hinitAT
        futureATime := hfutAT
        adminActionsDeadline := hdeadline
        transferOwnershipDeadline := htransfer
        futureFee := hfutFee
        futureAdminFee := hfutAdminFee
        futureOwner := hfutOwner
        isKilled := hkilled
        killDeadline := hkill }
      unlocked := hunlocked
      addr := ⟨hownerB, hcoinB0, hcoinB1, hcoinB2, htokenB, hfutOwnerB⟩ }

/-! ## The 3Crv checker -/

/-- The string checker: the length word, the length bound and the data words. -/
def checkVyStr (stor : Stor) (base : B256) (n : Nat) (bs : Bytes) : Bool :=
  decide ((stor.get base).toNat = bs.length) &&
  decide (bs.length ≤ 32 * n) &&
  decide (bs = (Lift.Curve3Crv.vyStrWords stor base n).take bs.length)

/-- **The 3Crv checker**: the footprint over the rows' words, each listed slot holding
its listed value, the fixed slots matching the base fields, and the supply equal to
the listed balance sum. -/
def checkC3 (stor : Stor) (rows : List C3Row) (base : C3Base) : Bool :=
  checkRows Lift.Curve3Crv.Key.slot Lift.Curve3Crv.vyFixedSlots (slotRows rows) stor &&
  rows.all (fun r => decide (stor.get r.2.1 = r.2.2)) &&
  decide (stor.get Lift.Curve3Crv.vyDecimalsSlot = base.decimals) &&
  decide (stor.get Lift.Curve3Crv.vySupplySlot = base.supply) &&
  decide (stor.get Lift.Curve3Crv.vyMinterSlot = base.minter.toB256) &&
  checkVyStr stor Lift.Curve3Crv.vyNameBase 2 base.name &&
  checkVyStr stor Lift.Curve3Crv.vySymbolBase 1 base.symbol &&
  decide (base.supply.toNat = rowsBalSum rows)

/-- **Soundness of the 3Crv checker.** -/
theorem checkC3_sound {rows : List C3Row} {stor : Stor} {base : C3Base}
    (h : checkC3 stor rows base = true) :
    Lift.Curve3Crv.VyInv stor (rowsState base rows) (c3Keys rows) := by
  simp only [checkC3, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hrows, hvals⟩, hdec⟩, hsup⟩, hminter⟩, hname⟩, hsym⟩, hsupply⟩ := h
  have sound := checkRows_sound hrows
  have nodup : (rows.map Prod.fst).Nodup := slotRows_keys rows ▸ sound.nodup
  have hname' : Lift.Curve3Crv.VyStr stor Lift.Curve3Crv.vyNameBase 2 base.name := by
    simp only [checkVyStr, Bool.and_eq_true, decide_eq_true_eq] at hname
    obtain ⟨⟨h1, h2⟩, h3⟩ := hname
    exact ⟨h1, h2, h3⟩
  have hsym' : Lift.Curve3Crv.VyStr stor Lift.Curve3Crv.vySymbolBase 1 base.symbol := by
    simp only [checkVyStr, Bool.and_eq_true, decide_eq_true_eq] at hsym
    obtain ⟨⟨h1, h2⟩, h3⟩ := hsym
    exact ⟨h1, h2, h3⟩
  refine
    { decimals := hdec
      supply := hsup
      minter := hminter
      name := hname'
      symbol := hsym'
      known := ?_
      unknown := ?_
      support := sound.support
      inj := sound.inj
      apart := sound.apart
      conserved := rowsState_conserved nodup hsupply }
  · intro k hk
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
    have hword : Lift.Curve3Crv.Key.slot r.1 = r.2.1 :=
      sound.word _ (List.mem_map_of_mem hr)
    change stor.get (Lift.Curve3Crv.Key.slot r.1) =
      Lift.Curve3Crv.Key.val (rowsState base rows) r.1
    rw [hword, rowsState_value, rowValue_of_mem nodup r hr]
    exact hvals r hr
  · intro k hk
    rw [rowsState_value]
    apply rowValue_of_not_mem
    change k ∉ (slotRows rows).map Prod.fst at hk
    rw [slotRows_keys] at hk
    exact hk

/-! ## The joint checkpoint and its checker -/

/-- **The joint checkpoint** (a predicate on one world state, however it was produced):
the pool's storage abstracts an unlocked model state whose `token` is the 3Crv
address, and 3Crv's storage abstracts a model state whose `minter` is the pool
address, over the live keys `K` (conservation rides along in `VyInv`). -/
structure JointCheckpoint (pool c3crv : Adr) (ps : Lift.Curve3Pool.State)
    (cs : Curve3Crv.State) (K : Lift.Curve3Crv.Key → Prop) (w : Jaune.State) : Prop where
  poolCk : Lift.Curve3Pool.Checkpoint (w.getStor pool) ps
  c3 : Lift.Curve3Crv.VyInv (w.getStor c3crv) cs K
  tokenIs : ps.token = c3crv.toNat
  minterIs : cs.minter = pool
  apart : pool ≠ c3crv

/-- **The joint checkpoint checker.** -/
def checkJoint (pool c3crv : Adr) (ps : Lift.Curve3Pool.State) (rows : List C3Row)
    (base : C3Base) (w : Jaune.State) : Bool :=
  checkPool (w.getStor pool) ps &&
  checkC3 (w.getStor c3crv) rows base &&
  decide (ps.token = c3crv.toNat) &&
  decide (base.minter = pool) &&
  decide (pool ≠ c3crv)

/-- **Soundness of the joint checkpoint checker.** -/
theorem checkJoint_sound {pool c3crv : Adr} {ps : Lift.Curve3Pool.State}
    {rows : List C3Row} {base : C3Base} {w : Jaune.State}
    (h : checkJoint pool c3crv ps rows base w = true) :
    JointCheckpoint pool c3crv ps (rowsState base rows) (c3Keys rows) w := by
  simp only [checkJoint, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hpool, hc3⟩, htoken⟩, hminter⟩, hapart⟩ := h
  exact
    { poolCk := checkPool_sound hpool
      c3 := checkC3_sound hc3
      tokenIs := htoken
      minterIs := hminter
      apart := hapart }

/-! ## One concrete synthetic world -/

/-- The synthetic pool address (not a precompile). -/
def poolAddr : Adr := 0x100

/-- The synthetic 3Crv address (not a precompile). -/
def c3crvAddr : Adr := 0x101

/-- The three synthetic coins standing in for DAI, USDC and USDT. -/
def coin0Addr : Adr := 0x200

/-- The three synthetic coins standing in for DAI, USDC and USDT. -/
def coin1Addr : Adr := 0x201

/-- The three synthetic coins standing in for DAI, USDC and USDT. -/
def coin2Addr : Adr := 0x202

/-- The single synthetic 3Crv holder. -/
def holderAddr : Adr := 0x300

/-- The synthetic pool owner. -/
def ownerAddr : Adr := 0x400

/-- The synthetic pool state: A = 100, fee = 4000000, admin_fee = 5000000000
(`admin_fee < 10^10`, so a later swap can raise D/T), small positive balances. -/
def poolState : Lift.Curve3Pool.State :=
  { coins := ⟨0x200, 0x201, 0x202⟩
    balances := ⟨1000, 2000, 3000⟩
    fee := 4000000
    adminFee := 5000000000
    owner := 0x400
    token := 0x101
    initialA := 100
    futureA := 100
    initialATime := 0
    futureATime := 0
    adminActionsDeadline := 0
    transferOwnershipDeadline := 0
    futureFee := 4000000
    futureAdminFee := 5000000000
    futureOwner := 0x400
    isKilled := false
    killDeadline := 0 }

/-- The synthetic 3Crv base fields: the pool is the minter, the supply is 6000. -/
def c3Base : C3Base :=
  { decimals := Nat.toB256 18
    supply := Nat.toB256 6000
    minter := poolAddr
    name := []
    symbol := [] }

/-- The synthetic 3Crv rows: the holder owns the whole 6000 supply. -/
def c3Rows : List C3Row :=
  [(Lift.Curve3Crv.Key.bal holderAddr,
    Lift.Curve3Crv.Key.slot (Lift.Curve3Crv.Key.bal holderAddr), Nat.toB256 6000)]

/-- The synthetic pool storage: every model slot, read off `poolState`. -/
def poolStor : Stor :=
  Stor.ofList
    [(Lift.Curve3Pool.coinSlot 0, Nat.toB256 0x200),
     (Lift.Curve3Pool.coinSlot 1, Nat.toB256 0x201),
     (Lift.Curve3Pool.coinSlot 2, Nat.toB256 0x202),
     (Lift.Curve3Pool.balanceSlot 0, Nat.toB256 1000),
     (Lift.Curve3Pool.balanceSlot 1, Nat.toB256 2000),
     (Lift.Curve3Pool.balanceSlot 2, Nat.toB256 3000),
     (Lift.Curve3Pool.feeSlot, Nat.toB256 4000000),
     (Lift.Curve3Pool.adminFeeSlot, Nat.toB256 5000000000),
     (Lift.Curve3Pool.ownerSlot, Nat.toB256 0x400),
     (Lift.Curve3Pool.tokenSlot, Nat.toB256 0x101),
     (Lift.Curve3Pool.initialASlot, Nat.toB256 100),
     (Lift.Curve3Pool.futureASlot, Nat.toB256 100),
     (Lift.Curve3Pool.initialATimeSlot, Nat.toB256 0),
     (Lift.Curve3Pool.futureATimeSlot, Nat.toB256 0),
     (Lift.Curve3Pool.adminActionsDeadlineSlot, Nat.toB256 0),
     (Lift.Curve3Pool.transferOwnershipDeadlineSlot, Nat.toB256 0),
     (Lift.Curve3Pool.futureFeeSlot, Nat.toB256 4000000),
     (Lift.Curve3Pool.futureAdminFeeSlot, Nat.toB256 5000000000),
     (Lift.Curve3Pool.futureOwnerSlot, Nat.toB256 0x400),
     (Lift.Curve3Pool.isKilledSlot, Lift.Curve3Pool.boolWord false),
     (Lift.Curve3Pool.killDeadlineSlot, Nat.toB256 0),
     (Lift.Curve3Pool.lockSlot, Nat.toB256 0)]

/-- The synthetic 3Crv storage: the fixed words and the holder's balance row. -/
def c3Stor : Stor :=
  Stor.ofList
    [(Lift.Curve3Crv.vyDecimalsSlot, Nat.toB256 18),
     (Lift.Curve3Crv.vySupplySlot, Nat.toB256 6000),
     (Lift.Curve3Crv.vyMinterSlot, poolAddr.toB256),
     (Lift.Curve3Crv.Key.slot (Lift.Curve3Crv.Key.bal holderAddr), Nat.toB256 6000)]

/-- The synthetic world: the pool and 3Crv accounts with the storages above. -/
def world : Jaune.State :=
  ((∅ : Jaune.State).setStor poolAddr poolStor).setStor c3crvAddr c3Stor

/-- The checker accepts the synthetic world (kernel evaluation). -/
theorem world_check : checkJoint poolAddr c3crvAddr poolState c3Rows c3Base world = true := by
  decide +kernel

/-- The synthetic world satisfies the joint checkpoint. -/
theorem world_joint :
    JointCheckpoint poolAddr c3crvAddr poolState (rowsState c3Base c3Rows)
      (c3Keys c3Rows) world :=
  checkJoint_sound world_check

end Blanc.Composition.Curve3Pool3CrvJoint
