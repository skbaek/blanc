-- DripAccounting.lean : DRIP's pure realized-accounting spine.
--
-- The frozen memo's R2 headline is an exact `Nat` equality over a finite
-- chain of adjacent ledger steps, and its R3 entitlement bound is that
-- equality's nonnegative corollary.  Both live here, above no execution and
-- below every concrete history lift, exactly as the goal's "pure Nat/storage
-- spine before concrete history lifts" rule asks.
--
-- Everything is parametric in the scale and in the realized index
-- transition.  That is the frozen rule that no concrete RAY number appears in
-- a generic lemma, and it is also what keeps these proofs free of 27-digit
-- numeral normalization.  The frozen instance is the corollary section at the
-- end, which fixes `scale.toNat` and `freshNat`.

import Blanc.DripRpow

namespace Blanc

open Jaune

namespace Drip

/-! ## Snapshots, kinds, and the surface floors -/

/-- One realized DRIP accounting snapshot: the two index words, the coalition's
normalized units, the total normalized supply, and the target's ETH balance. -/
structure Snapshot where
  chi : Nat
  rho : Nat
  coalitionUnits : Nat
  totalUnits : Nat
  balance : Nat

/-- The five exhaustive, mutually exclusive realized step kinds.  `counted`
records coalition membership of the acting address; an uncounted join or exit
still moves the total and the balance. -/
inductive Kind where
  | drip (elapsed : Nat)
  | join (counted : Bool) (actor : Adr) (assets units elapsed : Nat)
  | exit (counted : Bool) (actor : Adr) (units payout elapsed : Nat)
  | externalCredit (amount : Nat)
  | silent

/-- Units credited by a join of `assets` at index `chi`: the frozen floor. -/
def joinUnitsOf (scale assets chi : Nat) : Nat := assets * scale / chi

/-- The rounding residue that join floor leaves behind, in `scale`-units. -/
def joinResidueOf (scale assets chi : Nat) : Nat := assets * scale % chi

/-- Wei paid by an exit of `units` at index `chi`: the frozen floor. -/
def exitPayoutOf (scale units chi : Nat) : Nat := units * chi / scale

/-- The rounding residue that exit floor leaves behind. -/
def exitResidueOf (scale units chi : Nat) : Nat := units * chi % scale

theorem joinResidueOf_lt {scale assets chi : Nat} (hchi : chi ≠ 0) :
    joinResidueOf scale assets chi < chi :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero hchi)

theorem exitResidueOf_lt {scale units chi : Nat} (hscale : scale ≠ 0) :
    exitResidueOf scale units chi < scale :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero hscale)

/-! ## The adjacent-step carrier -/

/-- The exact effect of one realized adjacent step.  `drip`, `join` and `exit`
all advance the index by the same realized transition first — that is the
auto-drip the frozen memo requires — and only then convert.  An `exit` debits
its own row, the total and the balance at the settlement boundary; a positive
outside credit moves only the balance. -/
inductive Effect (scale : Nat) (fresh : Nat → Nat → Nat) :
    Snapshot → Kind → Snapshot → Prop where
  | drip (chi rho coalitionUnits totalUnits balance elapsed : Nat) :
      Effect scale fresh ⟨chi, rho, coalitionUnits, totalUnits, balance⟩
        (.drip elapsed)
        ⟨fresh chi elapsed, rho + elapsed, coalitionUnits, totalUnits, balance⟩
  | joinCounted (chi rho coalitionUnits totalUnits balance : Nat) (actor : Adr)
      (assets units elapsed : Nat)
      (quote : units = joinUnitsOf scale assets (fresh chi elapsed)) :
      Effect scale fresh ⟨chi, rho, coalitionUnits, totalUnits, balance⟩
        (.join true actor assets units elapsed)
        ⟨fresh chi elapsed, rho + elapsed, coalitionUnits + units,
          totalUnits + units, balance + assets⟩
  | joinOutside (chi rho coalitionUnits totalUnits balance : Nat) (actor : Adr)
      (assets units elapsed : Nat)
      (quote : units = joinUnitsOf scale assets (fresh chi elapsed)) :
      Effect scale fresh ⟨chi, rho, coalitionUnits, totalUnits, balance⟩
        (.join false actor assets units elapsed)
        ⟨fresh chi elapsed, rho + elapsed, coalitionUnits,
          totalUnits + units, balance + assets⟩
  | exitCounted (chi rho coalitionUnits totalUnits balance : Nat) (actor : Adr)
      (units payout elapsed : Nat)
      (owned : units ≤ coalitionUnits) (total : units ≤ totalUnits)
      (funded : payout ≤ balance)
      (quote : payout = exitPayoutOf scale units (fresh chi elapsed)) :
      Effect scale fresh ⟨chi, rho, coalitionUnits, totalUnits, balance⟩
        (.exit true actor units payout elapsed)
        ⟨fresh chi elapsed, rho + elapsed, coalitionUnits - units,
          totalUnits - units, balance - payout⟩
  | exitOutside (chi rho coalitionUnits totalUnits balance : Nat) (actor : Adr)
      (units payout elapsed : Nat)
      (total : units ≤ totalUnits) (funded : payout ≤ balance)
      (quote : payout = exitPayoutOf scale units (fresh chi elapsed)) :
      Effect scale fresh ⟨chi, rho, coalitionUnits, totalUnits, balance⟩
        (.exit false actor units payout elapsed)
        ⟨fresh chi elapsed, rho + elapsed, coalitionUnits,
          totalUnits - units, balance - payout⟩
  | externalCredit (chi rho coalitionUnits totalUnits balance amount : Nat)
      (positive : 0 < amount) :
      Effect scale fresh ⟨chi, rho, coalitionUnits, totalUnits, balance⟩
        (.externalCredit amount)
        ⟨chi, rho, coalitionUnits, totalUnits, balance + amount⟩
  | silent (snapshot : Snapshot) :
      Effect scale fresh snapshot .silent snapshot

/-- One realized adjacent step, carrying its own classification proof. -/
structure Step (scale : Nat) (fresh : Nat → Nat → Nat) where
  pre : Snapshot
  kind : Kind
  post : Snapshot
  effect : Effect scale fresh pre kind post

namespace Step

variable {scale : Nat} {fresh : Nat → Nat → Nat}

/-- Legitimate index accrual on the coalition's own units. -/
def accrual (step : Step scale fresh) : Nat :=
  match step.kind with
  | .drip _ | .join .. | .exit .. =>
      step.pre.coalitionUnits * (step.post.chi - step.pre.chi)
  | .externalCredit _ | .silent => 0

/-- Principal the coalition spent acquiring units. -/
def joined (step : Step scale fresh) : Nat :=
  match step.kind with
  | .join true _ assets _ _ => assets
  | _ => 0

/-- Rounding residue left by the coalition's own joins. -/
def joinResidue (step : Step scale fresh) : Nat :=
  match step.kind with
  | .join true _ assets _ _ => joinResidueOf scale assets step.post.chi
  | _ => 0

/-- Wei the coalition actually received. -/
def paid (step : Step scale fresh) : Nat :=
  match step.kind with
  | .exit true _ _ payout _ => payout
  | _ => 0

/-- Rounding residue left by the coalition's own exits. -/
def exitResidue (step : Step scale fresh) : Nat :=
  match step.kind with
  | .exit true _ units _ _ => exitResidueOf scale units step.post.chi
  | _ => 0

/-- Principal every participant spent, coalition or not. -/
def allJoined (step : Step scale fresh) : Nat :=
  match step.kind with
  | .join _ _ assets _ _ => assets
  | _ => 0

/-- Wei every participant received, coalition or not. -/
def allPaid (step : Step scale fresh) : Nat :=
  match step.kind with
  | .exit _ _ _ payout _ => payout
  | _ => 0

/-- Value credited from outside the ledger's own operations. -/
def gift (step : Step scale fresh) : Nat :=
  match step.kind with
  | .externalCredit amount => amount
  | _ => 0

private theorem accrue_eq (units chi chi' : Nat) (h : chi ≤ chi') :
    units * chi + units * (chi' - chi) = units * chi' := by
  rw [← Nat.mul_add, Nat.add_sub_of_le h]

private theorem join_decomposition (scale assets chi : Nat) :
    chi * joinUnitsOf scale assets chi + joinResidueOf scale assets chi =
      assets * scale :=
  Nat.div_add_mod (assets * scale) chi

private theorem exit_decomposition (scale units chi : Nat) :
    scale * exitPayoutOf scale units chi + exitResidueOf scale units chi =
      units * chi :=
  Nat.div_add_mod (units * chi) scale

/-- **The adjacent-step accounting identity.**  Every realized step conserves
the coalition's `scale`-denominated position exactly: its post-index value
plus the residues it left and the wei it was paid equals its pre-index value
plus the accrual it earned and the principal it spent. -/
theorem accounting_exact (mono : ∀ chi k, chi ≤ fresh chi k)
    (step : Step scale fresh) :
    step.post.coalitionUnits * step.post.chi +
        step.joinResidue + scale * step.paid + step.exitResidue =
      step.pre.coalitionUnits * step.pre.chi +
        step.accrual + scale * step.joined := by
  rcases step with ⟨pre, kind, post, effect⟩
  cases effect with
  | drip chi rho cu total balance elapsed =>
      simp only [accrual, joined, joinResidue, paid, exitResidue,
        Nat.add_zero, Nat.mul_zero]
      exact (accrue_eq cu chi (fresh chi elapsed) (mono chi elapsed)).symm
  | joinCounted chi rho cu total balance actor assets units elapsed quote =>
      subst units
      simp only [accrual, joined, joinResidue, paid, exitResidue,
        Nat.add_zero, Nat.mul_zero]
      rw [Nat.add_mul, accrue_eq cu chi (fresh chi elapsed) (mono chi elapsed),
        Nat.add_assoc]
      rw [Nat.mul_comm (joinUnitsOf scale assets (fresh chi elapsed))]
      rw [join_decomposition, Nat.mul_comm assets scale]
  | joinOutside chi rho cu total balance actor assets units elapsed quote =>
      subst units
      simp only [accrual, joined, joinResidue, paid, exitResidue,
        Nat.add_zero, Nat.mul_zero]
      exact (accrue_eq cu chi (fresh chi elapsed) (mono chi elapsed)).symm
  | exitCounted chi rho cu total balance actor units payout elapsed
      owned htotal funded quote =>
      subst payout
      simp only [accrual, joined, joinResidue, paid, exitResidue,
        Nat.add_zero, Nat.mul_zero]
      rw [accrue_eq cu chi (fresh chi elapsed) (mono chi elapsed),
        Nat.add_assoc, exit_decomposition]
      rw [← Nat.add_mul, Nat.sub_add_cancel owned]
  | exitOutside chi rho cu total balance actor units payout elapsed
      htotal funded quote =>
      subst payout
      simp only [accrual, joined, joinResidue, paid, exitResidue,
        Nat.add_zero, Nat.mul_zero]
      exact (accrue_eq cu chi (fresh chi elapsed) (mono chi elapsed)).symm
  | externalCredit chi rho cu total balance amount positive =>
      simp [accrual, joined, joinResidue, paid, exitResidue]
  | silent snapshot =>
      simp [accrual, joined, joinResidue, paid, exitResidue]

/-- **The adjacent-step balance identity.**  Every realized step moves the
target's balance by exactly what it paid out, took in, and was given. -/
theorem balance_exact (step : Step scale fresh) :
    step.post.balance + step.allPaid =
      step.pre.balance + step.allJoined + step.gift := by
  rcases step with ⟨pre, kind, post, effect⟩
  cases effect with
  | drip => simp [allPaid, allJoined, gift]
  | joinCounted => simp [allPaid, allJoined, gift]
  | joinOutside => simp [allPaid, allJoined, gift]
  | exitCounted chi rho cu total balance actor units payout elapsed
      owned htotal funded quote =>
      simp only [allPaid, allJoined, gift, Nat.add_zero]
      exact Nat.sub_add_cancel funded
  | exitOutside chi rho cu total balance actor units payout elapsed
      htotal funded quote =>
      simp only [allPaid, allJoined, gift, Nat.add_zero]
      exact Nat.sub_add_cancel funded
  | externalCredit => simp [allPaid, allJoined, gift]
  | silent => simp [allPaid, allJoined, gift]

/-- Every realized step leaves the index nondecreasing.  This is R4's step
case, stated where the carrier lives. -/
theorem chi_mono (mono : ∀ chi k, chi ≤ fresh chi k)
    (step : Step scale fresh) : step.pre.chi ≤ step.post.chi := by
  rcases step with ⟨pre, kind, post, effect⟩
  cases effect with
  | drip chi _ _ _ _ elapsed => exact mono chi elapsed
  | joinCounted chi _ _ _ _ _ _ _ elapsed => exact mono chi elapsed
  | joinOutside chi _ _ _ _ _ _ _ elapsed => exact mono chi elapsed
  | exitCounted chi _ _ _ _ _ _ _ elapsed => exact mono chi elapsed
  | exitOutside chi _ _ _ _ _ _ _ elapsed => exact mono chi elapsed
  | externalCredit => exact Nat.le_refl _
  | silent => exact Nat.le_refl _

/-- A counted exit's settled receipt, without reducing the payout term. -/
theorem paid_exitCounted (step : Step scale fresh) {actor : Adr}
    {units payout elapsed : Nat}
    (hkind : step.kind = .exit true actor units payout elapsed) :
    step.paid = payout := by
  unfold paid
  rw [hkind]

/-- A pure-drip step's accrual, without reducing the index transition. -/
theorem accrual_drip {k : Nat} (step : Step scale fresh)
    (hkind : step.kind = .drip k) :
    step.accrual =
      step.pre.coalitionUnits * (step.post.chi - step.pre.chi) := by
  unfold accrual
  rw [hkind]

/-- Every realized step leaves the clock nondecreasing. -/
theorem rho_mono (step : Step scale fresh) : step.pre.rho ≤ step.post.rho := by
  rcases step with ⟨pre, kind, post, effect⟩
  cases effect with
  | drip _ rho _ _ _ elapsed => exact Nat.le_add_right rho elapsed
  | joinCounted _ rho _ _ _ _ _ _ elapsed => exact Nat.le_add_right rho elapsed
  | joinOutside _ rho _ _ _ _ _ _ elapsed => exact Nat.le_add_right rho elapsed
  | exitCounted _ rho _ _ _ _ _ _ elapsed => exact Nat.le_add_right rho elapsed
  | exitOutside _ rho _ _ _ _ _ _ elapsed => exact Nat.le_add_right rho elapsed
  | externalCredit => exact Nat.le_refl _
  | silent => exact Nat.le_refl _

end Step

/-! ## Finite realized chains

A chain is a finite list of adjacent steps whose endpoints match.  Its totals
are the memo's `Acc_A`, `Join_A`, `Paid_A`, `JRes_A`, `ERes_A` and `Gift`, and
the two headline identities telescope the adjacent ones over it. -/

/-- A finite realized replay from `s` to `t`. -/
inductive Chain (scale : Nat) (fresh : Nat → Nat → Nat) :
    Snapshot → List (Step scale fresh) → Snapshot → Prop where
  | nil (s : Snapshot) : Chain scale fresh s [] s
  | cons {s t : Snapshot} {step : Step scale fresh}
      {rest : List (Step scale fresh)}
      (entry : step.pre = s) (tail : Chain scale fresh step.post rest t) :
      Chain scale fresh s (step :: rest) t

namespace Chain

variable {scale : Nat} {fresh : Nat → Nat → Nat}

/-- `Acc_A`: legitimate realized index accrual on the coalition's units. -/
def accrualSum (steps : List (Step scale fresh)) : Nat :=
  (steps.map Step.accrual).sum

/-- `Join_A`: principal the coalition spent acquiring units. -/
def joinedSum (steps : List (Step scale fresh)) : Nat :=
  (steps.map Step.joined).sum

/-- `JRes_A`: rounding residue the coalition's joins left behind. -/
def joinResidueSum (steps : List (Step scale fresh)) : Nat :=
  (steps.map Step.joinResidue).sum

/-- `Paid_A`: wei the coalition actually received. -/
def paidSum (steps : List (Step scale fresh)) : Nat :=
  (steps.map Step.paid).sum

/-- `ERes_A`: rounding residue the coalition's exits left behind. -/
def exitResidueSum (steps : List (Step scale fresh)) : Nat :=
  (steps.map Step.exitResidue).sum

/-- Principal every participant spent. -/
def allJoinedSum (steps : List (Step scale fresh)) : Nat :=
  (steps.map Step.allJoined).sum

/-- Wei every participant received. -/
def allPaidSum (steps : List (Step scale fresh)) : Nat :=
  (steps.map Step.allPaid).sum

/-- `Gift`: value credited from outside the ledger's own operations. -/
def giftSum (steps : List (Step scale fresh)) : Nat :=
  (steps.map Step.gift).sum

@[simp] theorem accrualSum_nil :
    accrualSum ([] : List (Step scale fresh)) = 0 := rfl
@[simp] theorem accrualSum_cons (step : Step scale fresh) (rest) :
    accrualSum (step :: rest) = step.accrual + accrualSum rest := rfl
@[simp] theorem joinedSum_nil :
    joinedSum ([] : List (Step scale fresh)) = 0 := rfl
@[simp] theorem joinedSum_cons (step : Step scale fresh) (rest) :
    joinedSum (step :: rest) = step.joined + joinedSum rest := rfl
@[simp] theorem joinResidueSum_nil :
    joinResidueSum ([] : List (Step scale fresh)) = 0 := rfl
@[simp] theorem joinResidueSum_cons (step : Step scale fresh) (rest) :
    joinResidueSum (step :: rest) = step.joinResidue + joinResidueSum rest := rfl
@[simp] theorem paidSum_nil :
    paidSum ([] : List (Step scale fresh)) = 0 := rfl
@[simp] theorem paidSum_cons (step : Step scale fresh) (rest) :
    paidSum (step :: rest) = step.paid + paidSum rest := rfl
@[simp] theorem exitResidueSum_nil :
    exitResidueSum ([] : List (Step scale fresh)) = 0 := rfl
@[simp] theorem exitResidueSum_cons (step : Step scale fresh) (rest) :
    exitResidueSum (step :: rest) = step.exitResidue + exitResidueSum rest := rfl
@[simp] theorem allJoinedSum_nil :
    allJoinedSum ([] : List (Step scale fresh)) = 0 := rfl
@[simp] theorem allJoinedSum_cons (step : Step scale fresh) (rest) :
    allJoinedSum (step :: rest) = step.allJoined + allJoinedSum rest := rfl
@[simp] theorem allPaidSum_nil :
    allPaidSum ([] : List (Step scale fresh)) = 0 := rfl
@[simp] theorem allPaidSum_cons (step : Step scale fresh) (rest) :
    allPaidSum (step :: rest) = step.allPaid + allPaidSum rest := rfl
@[simp] theorem giftSum_nil :
    giftSum ([] : List (Step scale fresh)) = 0 := rfl
@[simp] theorem giftSum_cons (step : Step scale fresh) (rest) :
    giftSum (step :: rest) = step.gift + giftSum rest := rfl

/-- **R2, the headline coalition identity.**  Over an arbitrary finite
realized replay, the coalition's `scale`-denominated closing position plus its
join residues, its settled receipts and its exit residues equals its opening
position plus its realized index accrual and the principal it spent.  Nothing
is approximated and nothing is dropped: `Nat` subtraction never appears. -/
theorem accounting_exact (mono : ∀ chi k, chi ≤ fresh chi k)
    {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t) :
    t.coalitionUnits * t.chi + joinResidueSum steps +
        scale * paidSum steps + exitResidueSum steps =
      s.coalitionUnits * s.chi + accrualSum steps +
        scale * joinedSum steps := by
  induction chain with
  | nil s => simp
  | cons entry tail ih =>
      rename_i s t step rest
      have hstep := Step.accounting_exact mono step
      rw [← entry]
      simp only [joinResidueSum_cons, paidSum_cons, exitResidueSum_cons,
        accrualSum_cons, joinedSum_cons, Nat.mul_add]
      omega

/-- **R2, the target-balance telescope.**  The target's closing balance plus
everything it paid out equals its opening balance, everything joined into it,
and every outside credit — so no payout can be funded from thin air and no
gift can be hidden inside a rounding conclusion. -/
theorem balance_exact {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t) :
    t.balance + allPaidSum steps =
      s.balance + allJoinedSum steps + giftSum steps := by
  induction chain with
  | nil s => simp
  | cons entry tail ih =>
      rename_i s t step rest
      have hstep := Step.balance_exact step
      rw [← entry]
      simp only [allPaidSum_cons, allJoinedSum_cons, giftSum_cons]
      omega

/-- **R4 at chain altitude.**  Every realized replay leaves the index
nondecreasing. -/
theorem chi_mono (mono : ∀ chi k, chi ≤ fresh chi k)
    {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t) : s.chi ≤ t.chi := by
  induction chain with
  | nil s => exact Nat.le_refl _
  | cons entry tail ih =>
      rename_i s t step rest
      rw [← entry]
      exact Nat.le_trans (Step.chi_mono mono step) ih

/-- **R4 at chain altitude.**  Every realized replay leaves the clock
nondecreasing. -/
theorem rho_mono {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t) : s.rho ≤ t.rho := by
  induction chain with
  | nil s => exact Nat.le_refl _
  | cons entry tail ih =>
      rename_i s t step rest
      rw [← entry]
      exact Nat.le_trans (Step.rho_mono step) ih

/-! ## R3 — no strategy can extract more than its entitlement -/

/-- **R3's entitlement bound, in `scale` units.**  A coalition that starts
with no units cannot settle more wei than its own principal plus its realized
index accrual buys.  This is the direct nonnegative corollary of the exact
identity: the closing position, the join residues and the exit residues are
all nonnegative and are simply dropped. -/
theorem scaled_entitlement (mono : ∀ chi k, chi ≤ fresh chi k)
    {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t)
    (fresh_start : s.coalitionUnits = 0) :
    scale * paidSum steps ≤ accrualSum steps + scale * joinedSum steps := by
  have hexact := accounting_exact mono chain
  rw [fresh_start, Nat.zero_mul] at hexact
  omega

/-- **R3's entitlement bound, in wei.**  Settled receipts never exceed the
principal spent plus the floor of realized accrual — so no surface floor and
no boundary placement can create surplus. -/
theorem entitlement (mono : ∀ chi k, chi ≤ fresh chi k)
    (scale_pos : 0 < scale)
    {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t)
    (fresh_start : s.coalitionUnits = 0) :
    paidSum steps ≤ joinedSum steps + accrualSum steps / scale := by
  have hscaled := scaled_entitlement mono chain fresh_start
  by_cases hle : paidSum steps ≤ joinedSum steps
  · exact Nat.le_trans hle (Nat.le_add_right _ _)
  · have hgt : joinedSum steps < paidSum steps := Nat.lt_of_not_le hle
    have hdiff : scale * (paidSum steps - joinedSum steps) ≤ accrualSum steps := by
      rw [Nat.mul_sub]
      omega
    have hquot : paidSum steps - joinedSum steps ≤ accrualSum steps / scale :=
      (Nat.le_div_iff_mul_le scale_pos).2 (by rw [Nat.mul_comm]; exact hdiff)
    omega

end Chain

/-! ## Aggregate floor behaviour -/

/-- **Floor-sum subadditivity at a common realized index.**  Splitting a
position across rows can only lose wei to the floor, never gain: the sum of
the individual floor payouts is at most the floor payout of the summed units.
This is Jaune's two-term law, folded. -/
theorem exitPayoutOf_sum_le (scale chi : Nat) (units : List Nat) :
    (units.map (fun u => exitPayoutOf scale u chi)).sum ≤
      exitPayoutOf scale units.sum chi := by
  induction units with
  | nil => simp [exitPayoutOf]
  | cons u rest ih =>
      simp only [List.map_cons, List.sum_cons, exitPayoutOf] at ih ⊢
      calc u * chi / scale + (rest.map (fun v => v * chi / scale)).sum
          ≤ u * chi / scale + rest.sum * chi / scale :=
            Nat.add_le_add_left ih _
        _ ≤ (u * chi + rest.sum * chi) / scale :=
            Jaune.Nat.div_add_div_le_add_div _ _ _
        _ = (u + rest.sum) * chi / scale := by rw [Nat.add_mul]

namespace Step

variable {scale : Nat} {fresh : Nat → Nat → Nat}

/-- A step's own join residue is strictly below the index it converted at. -/
theorem joinResidue_lt (step : Step scale fresh)
    (hchi : 0 < step.post.chi) : step.joinResidue < step.post.chi := by
  unfold joinResidue
  split
  · exact Nat.mod_lt _ hchi
  · exact hchi

/-- A step's own exit residue is strictly below the scale. -/
theorem exitResidue_lt (step : Step scale fresh)
    (hscale : 0 < scale) : step.exitResidue < scale := by
  unfold exitResidue
  split
  · exact Nat.mod_lt _ hscale
  · exact hscale

end Step

/-! ## The frozen DRIP instance

Every generic result above is instantiated once here at the approved
constants.  `freshNat_mono` is Jaune's base-preservation and floor-composition
result at DRIP's `S ≤ R`; `scaleNat_ne_zero` is the frozen ray scale. -/

/-- A realized DRIP step at the frozen scale and index transition. -/
abbrev RealizedStep : Type := Step scale.toNat freshNat

/-- A finite realized DRIP replay at the frozen scale and index transition. -/
abbrev RealizedChain : Snapshot → List RealizedStep → Snapshot → Prop :=
  Chain scale.toNat freshNat

theorem realized_freshNat_mono : ∀ chi k, chi ≤ freshNat chi k :=
  fun chi k => freshNat_mono chi k

/-- R2's headline coalition identity at the frozen DRIP constants. -/
theorem coalition_accounting_exact {s t : Snapshot} {steps : List RealizedStep}
    (chain : RealizedChain s steps t) :
    t.coalitionUnits * t.chi + Chain.joinResidueSum steps +
        scale.toNat * Chain.paidSum steps + Chain.exitResidueSum steps =
      s.coalitionUnits * s.chi + Chain.accrualSum steps +
        scale.toNat * Chain.joinedSum steps :=
  Chain.accounting_exact realized_freshNat_mono chain

/-- R2's target-balance telescope at the frozen DRIP constants. -/
theorem target_balance_exact {s t : Snapshot} {steps : List RealizedStep}
    (chain : RealizedChain s steps t) :
    t.balance + Chain.allPaidSum steps =
      s.balance + Chain.allJoinedSum steps + Chain.giftSum steps :=
  Chain.balance_exact chain

/-- R3's entitlement bound at the frozen DRIP constants: a coalition that
starts with no units never settles more wei than the principal it spent plus
the floor of its realized index accrual. -/
theorem coalition_entitlement {s t : Snapshot} {steps : List RealizedStep}
    (chain : RealizedChain s steps t) (fresh_start : s.coalitionUnits = 0) :
    Chain.paidSum steps ≤
      Chain.joinedSum steps + Chain.accrualSum steps / scale.toNat :=
  Chain.entitlement realized_freshNat_mono
    (Nat.pos_of_ne_zero scaleNat_ne_zero) chain fresh_start

/-- The `scale`-denominated form of the same bound. -/
theorem coalition_scaled_entitlement {s t : Snapshot} {steps : List RealizedStep}
    (chain : RealizedChain s steps t) (fresh_start : s.coalitionUnits = 0) :
    scale.toNat * Chain.paidSum steps ≤
      Chain.accrualSum steps + scale.toNat * Chain.joinedSum steps :=
  Chain.scaled_entitlement realized_freshNat_mono chain fresh_start

/-- R4's realized-index projection at the frozen DRIP constants. -/
theorem realized_chi_mono {s t : Snapshot} {steps : List RealizedStep}
    (chain : RealizedChain s steps t) : s.chi ≤ t.chi :=
  Chain.chi_mono realized_freshNat_mono chain

/-- R4's realized-clock projection at the frozen DRIP constants. -/
theorem realized_rho_mono {s t : Snapshot} {steps : List RealizedStep}
    (chain : RealizedChain s steps t) : s.rho ≤ t.rho :=
  Chain.rho_mono chain


/-! ## Same-timestamp identities -/

/-- The frozen factor at zero elapsed time is the scale itself: a
same-timestamp call performs the identity accrual. -/
theorem factorNat_zero : factorNat 0 = scale.toNat := by
  unfold factorNat Jaune.rpow
  split <;> rfl

/-- A same-timestamp operation leaves the realized index exactly where it
was.  Repeated calls in one block are therefore exact identities, not a
rounding opportunity. -/
theorem freshNat_zero (chi : Nat) : freshNat chi 0 = chi := by
  unfold freshNat
  rw [factorNat_zero]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero scaleNat_ne_zero)

private theorem scale_pos : 0 < scale.toNat :=
  Nat.pos_of_ne_zero scaleNat_ne_zero

private theorem freshNat_three :
    freshNat scale.toNat 3 = 1000000004641377880770433536 := by
  unfold freshNat
  rw [factorNat_three_exact, Nat.mul_comm, Nat.mul_div_cancel _ scale_pos]

private theorem scale_lt_freshNat_three :
    scale.toNat < freshNat scale.toNat 3 := by
  rw [freshNat_three, scaleNat_exact]
  decide +kernel

/-! ## Anti-vacuity: a concrete inhabited realized trace -/

private def ofEffect {scale : Nat} {fresh : Nat → Nat → Nat}
    {pre : Snapshot} {kind : Kind} {post : Snapshot}
    (effect : Effect scale fresh pre kind post) : Step scale fresh :=
  ⟨pre, kind, post, effect⟩

private theorem witnessJoinQuote :
    scale.toNat = joinUnitsOf scale.toNat scale.toNat (freshNat scale.toNat 0) := by
  rw [freshNat_zero, joinUnitsOf, Nat.mul_div_cancel _ scale_pos]

private theorem witnessGiftPositive :
    0 < freshNat (freshNat scale.toNat 0) 3 := by
  rw [freshNat_zero, freshNat_three]
  decide +kernel

private theorem witnessExitFunded :
    exitPayoutOf scale.toNat scale.toNat
        (freshNat (freshNat (freshNat scale.toNat 0) 3) 0) ≤
      0 + scale.toNat + freshNat (freshNat scale.toNat 0) 3 := by
  rw [freshNat_zero, freshNat_zero, exitPayoutOf, Nat.mul_comm,
    Nat.mul_div_cancel _ scale_pos]
  exact Nat.le_add_left _ _

/-- Alice joins at genesis with one ray of ether. -/
private def witnessJoin (actor : Adr) : RealizedStep :=
  ofEffect (Effect.joinCounted (scale := scale.toNat) (fresh := freshNat)
    scale.toNat 0 0 0 0 actor scale.toNat scale.toNat 0 witnessJoinQuote)

/-- Three seconds pass and anyone drips. -/
private def witnessDrip : RealizedStep :=
  ofEffect (Effect.drip (scale := scale.toNat) (fresh := freshNat)
    (freshNat scale.toNat 0) (0 + 0) (0 + scale.toNat) (0 + scale.toNat)
    (0 + scale.toNat) 3)

/-- An outside donation funds the accrued entitlement. -/
private def witnessGift : RealizedStep :=
  ofEffect (Effect.externalCredit (scale := scale.toNat) (fresh := freshNat)
    (freshNat (freshNat scale.toNat 0) 3) (0 + 0 + 3) (0 + scale.toNat)
    (0 + scale.toNat) (0 + scale.toNat)
    (freshNat (freshNat scale.toNat 0) 3) witnessGiftPositive)

/-- Alice exits her whole row at the realized index. -/
private def witnessExit (actor : Adr) : RealizedStep :=
  ofEffect (Effect.exitCounted (scale := scale.toNat) (fresh := freshNat)
    (freshNat (freshNat scale.toNat 0) 3) (0 + 0 + 3) (0 + scale.toNat)
    (0 + scale.toNat) (0 + scale.toNat + freshNat (freshNat scale.toNat 0) 3)
    actor scale.toNat
    (exitPayoutOf scale.toNat scale.toNat
      (freshNat (freshNat (freshNat scale.toNat 0) 3) 0)) 0
    (Nat.le_add_left _ _) (Nat.le_add_left _ _) witnessExitFunded rfl)

private def witnessSteps (actor : Adr) : List RealizedStep :=
  [witnessJoin actor, witnessDrip, witnessGift, witnessExit actor]

private theorem witnessChain (actor : Adr) :
    RealizedChain (witnessJoin actor).pre (witnessSteps actor)
      (witnessExit actor).post :=
  .cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))

private theorem joinedJoin (actor : Adr) :
    Step.joined (witnessJoin actor) = scale.toNat := rfl
private theorem joinedDrip : Step.joined witnessDrip = 0 := rfl
private theorem joinedGift : Step.joined witnessGift = 0 := rfl
private theorem joinedExit (actor : Adr) :
    Step.joined (witnessExit actor) = 0 := rfl


private theorem giftJoin (actor : Adr) :
    Step.gift (witnessJoin actor) = 0 := rfl
private theorem giftDrip : Step.gift witnessDrip = 0 := rfl
private theorem giftGift :
    Step.gift witnessGift = freshNat (freshNat scale.toNat 0) 3 := rfl
private theorem giftExit (actor : Adr) :
    Step.gift (witnessExit actor) = 0 := rfl


private theorem paidJoin (actor : Adr) :
    Step.paid (witnessJoin actor) = 0 := rfl
private theorem paidDrip : Step.paid witnessDrip = 0 := rfl
private theorem paidGift : Step.paid witnessGift = 0 := rfl
private theorem paidExit (actor : Adr) :
    Step.paid (witnessExit actor) =
      exitPayoutOf scale.toNat scale.toNat
        (freshNat (freshNat (freshNat scale.toNat 0) 3) 0) :=
  Step.paid_exitCounted (witnessExit actor) rfl


private theorem accrualDripPos : 0 < Step.accrual witnessDrip := by
  have hkind : witnessDrip.kind = Kind.drip 3 := rfl
  have hcu : witnessDrip.pre.coalitionUnits = 0 + scale.toNat := rfl
  have hpre : witnessDrip.pre.chi = freshNat scale.toNat 0 := rfl
  have hpost : witnessDrip.post.chi = freshNat (freshNat scale.toNat 0) 3 := rfl
  rw [Step.accrual_drip witnessDrip hkind, hcu, hpre, hpost, freshNat_zero]
  have hs := scale_pos
  have hlt := scale_lt_freshNat_three
  exact Nat.mul_pos (by omega) (by omega)

private theorem witnessJoinedSum (actor : Adr) :
    Chain.joinedSum (witnessSteps actor) = scale.toNat := by
  unfold witnessSteps
  rw [Chain.joinedSum_cons, Chain.joinedSum_cons, Chain.joinedSum_cons,
    Chain.joinedSum_cons, Chain.joinedSum_nil, joinedJoin, joinedDrip,
    joinedGift, joinedExit]
  omega

private theorem witnessGiftSum (actor : Adr) :
    Chain.giftSum (witnessSteps actor) = freshNat scale.toNat 3 := by
  unfold witnessSteps
  rw [Chain.giftSum_cons, Chain.giftSum_cons, Chain.giftSum_cons,
    Chain.giftSum_cons, Chain.giftSum_nil, giftJoin, giftDrip, giftGift,
    giftExit, freshNat_zero]
  omega

private theorem witnessPaidSum (actor : Adr) :
    Chain.paidSum (witnessSteps actor) = freshNat scale.toNat 3 := by
  unfold witnessSteps
  rw [Chain.paidSum_cons, Chain.paidSum_cons, Chain.paidSum_cons,
    Chain.paidSum_cons, Chain.paidSum_nil, paidJoin, paidDrip, paidGift,
    paidExit, freshNat_zero, freshNat_zero, exitPayoutOf, Nat.mul_comm,
    Nat.mul_div_cancel _ scale_pos]
  omega

private theorem witnessAccrualPos (actor : Adr) :
    0 < Chain.accrualSum (witnessSteps actor) := by
  have hdrip := accrualDripPos
  unfold witnessSteps
  rw [Chain.accrualSum_cons, Chain.accrualSum_cons, Chain.accrualSum_cons,
    Chain.accrualSum_cons, Chain.accrualSum_nil]
  omega

/-- **Anti-vacuity.**  The realized carrier is inhabited by a concrete
join / drip / donate / exit trace in which the coalition starts with nothing
and every headline total — principal spent, realized accrual, outside credit,
and settled receipt — is nonzero.  Without this the exact identity above could
hold of empty replays alone. -/
theorem realized_chain_inhabited (actor : Adr) :
    ∃ (s t : Snapshot) (steps : List RealizedStep),
      RealizedChain s steps t ∧ s.coalitionUnits = 0 ∧
        0 < Chain.joinedSum steps ∧ 0 < Chain.accrualSum steps ∧
        0 < Chain.giftSum steps ∧ 0 < Chain.paidSum steps := by
  have hs := scale_pos
  have hlt := scale_lt_freshNat_three
  refine ⟨(witnessJoin actor).pre, (witnessExit actor).post,
    witnessSteps actor, witnessChain actor, rfl, ?_, ?_, ?_, ?_⟩
  · rw [witnessJoinedSum]
    exact hs
  · exact witnessAccrualPos actor
  · rw [witnessGiftSum]
    omega
  · rw [witnessPaidSum]
    omega

end Drip

end Blanc
