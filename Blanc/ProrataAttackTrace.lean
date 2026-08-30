-- ProrataAttackTrace.lean : the SF-frozen P4 attack trace and its headlines.

import Blanc.ProrataAttackPath
import Blanc.ProrataAccountingHistory

namespace Blanc

open Jaune

namespace Prorata

/-! ## Compiled-offset side conditions

The pure P4 results are parametric in the virtual-share offset and carry `o ≠ 0`
or the stronger `2 ≤ o` as premises.  The realized layer instantiates them at
the compiled offset, which discharges both, so no realized headline below
carries an arithmetic premise. -/

theorem offset_ne_zero : offset.toNat ≠ 0 := by rw [offset_toNat]; omega

theorem two_le_offset : 2 ≤ offset.toNat := by rw [offset_toNat]; omega

/-- The genesis price anchor is exactly the backing bound.  `PriceLe o ⟨0,0⟩ s`
says the share price at `s` has not fallen below its genesis value `1/o`, and
that is the same statement as `supply ≤ o · balance` — the invariant's third
conjunct, available at every boundary of a genesis-rooted replay rather than
only at a settled world state. -/
theorem backed_of_priceLe_genesis {o : Nat} {s : AccountingSnapshot}
    (h : PriceLe o ⟨0, 0⟩ s) : s.supply ≤ o * s.balance := by
  have h1 : 1 * (s.supply + o) ≤ (s.balance + 1) * (0 + o) := h
  rw [Nat.one_mul, Nat.zero_add, Nat.add_mul, Nat.one_mul,
    Nat.mul_comm s.balance o] at h1
  omega

@[simp] theorem AttackAttribution.coalitionAmount_zero (a : AttackAttribution) :
    a.coalitionAmount 0 = 0 := by cases a <;> rfl

@[simp] theorem AttackAttribution.outsideAmount_zero (a : AttackAttribution) :
    a.outsideAmount 0 = 0 := by cases a <;> rfl

/-! ## Price monotonicity along a realized replay -/

namespace ProrataAccountingReplay

/-- Every step of a replay is priced no worse than the replay's own initial
boundary: the share price is nondecreasing, so the connected chain of step
boundaries carries the genesis anchor forward to each step in turn. -/
theorem priceLe_of_mem {o : Nat} (ho : o ≠ 0)
    {first last : RealizedSnapshot} {steps : List (ProrataAccountingStep o)}
    (replay : ProrataAccountingReplay o first steps last)
    {step : ProrataAccountingStep o} :
    step ∈ steps → PriceLe o first.snapshot step.pre := by
  induction replay with
  | nil boundary => intro mem; cases mem
  | @cons pre mid last hd tl pre_eq post_eq move tail ih =>
      intro mem
      have hstep : PriceLe o pre.snapshot mid.snapshot := by
        have h := ProrataAccountingEffect.priceLe ho hd.effect
        rwa [pre_eq, post_eq] at h
      rcases List.mem_cons.mp mem with rfl | hmem
      · rw [pre_eq]
        exact PriceLe.refl o pre.snapshot
      · exact PriceLe.trans ho hstep (ih hmem)

/-- Between the two members of a two-element filtered subsequence the price
never falls.  The earlier step's own post-boundary is a boundary of the replay,
so the later step inherits the anchor from it without any list surgery. -/
theorem priceLe_of_filter_pair {o : Nat} (ho : o ≠ 0)
    {first last : RealizedSnapshot} {steps : List (ProrataAccountingStep o)}
    (replay : ProrataAccountingReplay o first steps last)
    {p : ProrataAccountingStep o → Bool} {d w : ProrataAccountingStep o} :
    steps.filter p = [d, w] → PriceLe o d.post w.pre := by
  induction replay with
  | nil boundary => intro h; simp at h
  | @cons pre mid last hd tl pre_eq post_eq move tail ih =>
      intro h
      by_cases hp : p hd = true
      · rw [List.filter_cons_of_pos hp] at h
        simp only [List.cons.injEq] at h
        obtain ⟨rfl, htl⟩ := h
        have hw : w ∈ tl :=
          List.mem_of_mem_filter (p := p) (by rw [htl]; exact List.mem_singleton_self w)
        rw [post_eq]
        exact tail.priceLe_of_mem ho hw
      · rw [List.filter_cons_of_neg (by simpa using hp)] at h
        exact ih h

end ProrataAccountingReplay

/-! ## The victim's own moves

The SF closure restricts the victim's *economic* activity.  An observation
moves no value and is therefore not a victim move: a view call by the victim
stays admissible at every point of the trace. -/

/-- Whether a realized step is one of the victim's economic moves. -/
def victimMove {o : Nat} (victim : Adr) (step : ProrataAccountingStep o) : Bool :=
  decide (step.provenance.actor = some victim) && decide (step.kind ≠ .silent)

/-- The victim's economic moves, in trace order. -/
def victimMoves {o : Nat} (victim : Adr)
    (steps : List (ProrataAccountingStep o)) : List (ProrataAccountingStep o) :=
  steps.filter (victimMove victim)

theorem victimMoves_cons_of_move {o : Nat} {victim : Adr}
    {step : ProrataAccountingStep o} {steps : List (ProrataAccountingStep o)}
    (hactor : step.provenance.actor = some victim) (hkind : step.kind ≠ .silent) :
    victimMoves victim (step :: steps) = step :: victimMoves victim steps := by
  simp [victimMoves, victimMove, hactor, hkind]

theorem victimMoves_cons_of_foreign {o : Nat} {victim : Adr}
    {step : ProrataAccountingStep o} {steps : List (ProrataAccountingStep o)}
    (hactor : ¬ step.provenance.actor = some victim) :
    victimMoves victim (step :: steps) = victimMoves victim steps := by
  simp [victimMoves, victimMove, hactor]

theorem victimMoves_cons_of_silent {o : Nat} {victim : Adr}
    {step : ProrataAccountingStep o} {steps : List (ProrataAccountingStep o)}
    (hkind : step.kind = .silent) :
    victimMoves victim (step :: steps) = victimMoves victim steps := by
  simp [victimMoves, victimMove, hkind]

theorem mem_of_mem_victimMoves {o : Nat} {victim : Adr}
    {step : ProrataAccountingStep o} {steps : List (ProrataAccountingStep o)}
    (mem : step ∈ victimMoves victim steps) : step ∈ steps :=
  List.mem_of_mem_filter mem

/-- The SF-frozen victim schedule.

The trace contains exactly one successful victim deposit, and at most one later
successful full redemption of exactly the balance that deposit minted — the
zero-share case included, since `minted` is an arbitrary `Nat`.  Because the
list is the victim's *complete* move list in trace order, "later" is the order
itself and "no other victim activity" is the absence of any further entry: the
victim performs no second deposit, no other withdrawal, and no positive target
credit of its own.

This is a strategy/accounting closure over the victim's own moves.  It places
no honesty, cooperation or no-donation requirement on any callee, and no
requirement at all on what the rest of the world does. -/
def VictimSchedule {o : Nat} (victim : Adr)
    (steps : List (ProrataAccountingStep o)) : Prop :=
  ∃ (deposit : ProrataAccountingStep o) (amount minted : Nat),
    deposit.kind = .deposit amount minted ∧
      (victimMoves victim steps = [deposit] ∨
        ∃ (exit : ProrataAccountingStep o) (paid : Nat),
          exit.kind = .withdraw minted paid ∧
            victimMoves victim steps = [deposit, exit])

/-- The victim moves a reached phase still admits.  `before` is the frozen
schedule itself; `open` is what remains once the unique deposit has been seen;
`exited` admits nothing further. -/
def VictimPhase.Admits {o : Nat} (phase : VictimPhase o) (victim : Adr)
    (steps : List (ProrataAccountingStep o)) : Prop :=
  match phase with
  | .before => VictimSchedule victim steps
  | .open deposit =>
      victimMoves victim steps = [] ∨
        ∃ (exit : ProrataAccountingStep o) (paid : Nat),
          exit.kind = .withdraw deposit.minted paid ∧
            victimMoves victim steps = [exit]
  | .exited _ _ => victimMoves victim steps = []

/-- What a phase admits depends on the trace only through the victim's own
moves, so steps that are not victim moves drop out of it. -/
theorem VictimPhase.Admits.of_moves_eq {o : Nat} {phase : VictimPhase o}
    {victim : Adr} {steps steps' : List (ProrataAccountingStep o)}
    (h : victimMoves victim steps' = victimMoves victim steps)
    (hadmits : phase.Admits victim steps) : phase.Admits victim steps' := by
  cases phase <;>
    simp only [VictimPhase.Admits, VictimSchedule, h] <;>
    exact hadmits

/-- The unique victim deposit is admitted only before it has happened, and it
leaves exactly the optional full exit outstanding. -/
theorem victimDeposit_phase {o : Nat} {phase : VictimPhase o} {victim : Adr}
    {step : ProrataAccountingStep o} {rest : List (ProrataAccountingStep o)}
    {amount minted : Nat}
    (hadmits : phase.Admits victim (step :: rest))
    (hmoves : victimMoves victim (step :: rest) = step :: victimMoves victim rest)
    (hkind : step.kind = .deposit amount minted) :
    phase = .before ∧
      (victimMoves victim rest = [] ∨
        ∃ (exit : ProrataAccountingStep o) (paid : Nat),
          exit.kind = .withdraw minted paid ∧ victimMoves victim rest = [exit]) := by
  cases phase with
  | before =>
      obtain ⟨d, a, m, hdk, hshape⟩ := hadmits
      rw [hmoves] at hshape
      refine ⟨rfl, ?_⟩
      rcases hshape with h | ⟨w, p, hwk, h⟩
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, htl⟩ := h
        exact Or.inl htl
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, htl⟩ := h
        rw [hkind] at hdk
        cases hdk
        exact Or.inr ⟨w, p, hwk, htl⟩
  | «open» dep =>
      exfalso
      rcases hadmits with h | ⟨w, p, hwk, h⟩ <;> rw [hmoves] at h
      · simp at h
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [hkind] at hwk
        exact ProrataAccountingKind.noConfusion hwk
  | exited dep ex =>
      exfalso
      have h : victimMoves victim (step :: rest) = [] := hadmits
      rw [hmoves] at h
      simp at h

/-- The optional victim exit is admitted only while the deposit is open, burns
exactly the balance that deposit minted, and closes the victim's schedule. -/
theorem victimExit_phase {o : Nat} {phase : VictimPhase o} {victim : Adr}
    {step : ProrataAccountingStep o} {rest : List (ProrataAccountingStep o)}
    {shares paid : Nat}
    (hadmits : phase.Admits victim (step :: rest))
    (hmoves : victimMoves victim (step :: rest) = step :: victimMoves victim rest)
    (hkind : step.kind = .withdraw shares paid) :
    ∃ deposit : VictimDeposit o,
      phase = .open deposit ∧ shares = deposit.minted ∧
        victimMoves victim rest = [] := by
  cases phase with
  | before =>
      exfalso
      obtain ⟨d, a, m, hdk, hshape⟩ := hadmits
      rw [hmoves] at hshape
      rcases hshape with h | ⟨w, p, -, h⟩ <;>
        simp only [List.cons.injEq] at h <;>
        obtain ⟨rfl, -⟩ := h <;>
        rw [hkind] at hdk <;>
        exact ProrataAccountingKind.noConfusion hdk
  | «open» dep =>
      refine ⟨dep, rfl, ?_, ?_⟩ <;>
        rcases hadmits with h | ⟨w, p, hwk, h⟩ <;> rw [hmoves] at h
      · simp at h
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [hkind] at hwk
        injection hwk with hw _
      · simp at h
      · simp only [List.cons.injEq] at h
        exact h.2
  | exited dep ex =>
      exfalso
      have h : victimMoves victim (step :: rest) = [] := hadmits
      rw [hmoves] at h
      simp at h

/-- The victim makes no positive target credit of its own: the schedule admits
a deposit or a full exit, never a bare credit. -/
theorem victimCredit_absurd {o : Nat} {phase : VictimPhase o} {victim : Adr}
    {step : ProrataAccountingStep o} {rest : List (ProrataAccountingStep o)}
    {amount : Nat}
    (hadmits : phase.Admits victim (step :: rest))
    (hmoves : victimMoves victim (step :: rest) = step :: victimMoves victim rest)
    (hkind : step.kind = .externalCredit amount) : False := by
  cases phase with
  | before =>
      obtain ⟨d, a, m, hdk, hshape⟩ := hadmits
      rw [hmoves] at hshape
      rcases hshape with h | ⟨w, p, -, h⟩ <;>
        simp only [List.cons.injEq] at h <;>
        obtain ⟨rfl, -⟩ := h <;>
        rw [hkind] at hdk <;>
        exact ProrataAccountingKind.noConfusion hdk
  | «open» dep =>
      rcases hadmits with h | ⟨w, p, hwk, h⟩ <;> rw [hmoves] at h
      · simp at h
      · simp only [List.cons.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [hkind] at hwk
        exact ProrataAccountingKind.noConfusion hwk
  | exited dep ex =>
      have h : victimMoves victim (step :: rest) = [] := hadmits
      rw [hmoves] at h
      simp at h

/-! ## Coalition accounting over a realized trace -/

/-- The settled principal one step credits to PRORATA on a non-victim account:
a non-victim deposit's value or a non-victim positive target credit. -/
def stepCredit {o : Nat} (victim : Adr) (step : ProrataAccountingStep o) : Nat :=
  if step.provenance.actor = some victim then 0
  else
    match step.kind with
    | .deposit amount _ => amount
    | .externalCredit amount => amount
    | .withdraw _ _ => 0
    | .silent => 0

/-- The settled principal one step pays out on a non-victim account. -/
def stepPayout {o : Nat} (victim : Adr) (step : ProrataAccountingStep o) : Nat :=
  if step.provenance.actor = some victim then 0
  else
    match step.kind with
    | .withdraw _ paid => paid
    | .deposit _ _ => 0
    | .externalCredit _ => 0
    | .silent => 0

/-- `inA`: exactly the settled deposits and positive target credits attributed
to the coalition. -/
def inA {o : Nat} (victim : Adr)
    (charge : ProrataAccountingStep o → AttackAttribution)
    (steps : List (ProrataAccountingStep o)) : Nat :=
  (steps.map fun step => (charge step).coalitionAmount (stepCredit victim step)).sum

/-- `outA`: exactly the settled PRORATA withdrawals paid to the coalition. -/
def outA {o : Nat} (victim : Adr)
    (charge : ProrataAccountingStep o → AttackAttribution)
    (steps : List (ProrataAccountingStep o)) : Nat :=
  (steps.map fun step => (charge step).coalitionAmount (stepPayout victim step)).sum

/-- `outsideSubsidy`: exactly the settled positive credits charged to neither
the coalition nor the designated victim deposit. -/
def outsideSubsidy {o : Nat} (victim : Adr)
    (charge : ProrataAccountingStep o → AttackAttribution)
    (steps : List (ProrataAccountingStep o)) : Nat :=
  (steps.map fun step => (charge step).outsideAmount (stepCredit victim step)).sum

/-- The charge assignment of a closed trace: every non-victim flow is the
coalition's, so the diagnostic subsidy term is identically zero. -/
def coalitionCharge {o : Nat} : ProrataAccountingStep o → AttackAttribution :=
  fun _ => .coalition

theorem outsideSubsidy_coalitionCharge {o : Nat} (victim : Adr)
    (steps : List (ProrataAccountingStep o)) :
    outsideSubsidy victim coalitionCharge steps = 0 := by
  induction steps with
  | nil => rfl
  | cons s ss ih => simp [outsideSubsidy, coalitionCharge,
      AttackAttribution.outsideAmount]

/-- At the closed charge the coalition's input is exactly the sum of every
settled non-victim deposit value and positive target credit. -/
theorem inA_coalitionCharge {o : Nat} (victim : Adr)
    (steps : List (ProrataAccountingStep o)) :
    inA victim coalitionCharge steps = (steps.map (stepCredit victim)).sum := rfl

/-- At the closed charge the coalition's take is exactly the sum of every
settled non-victim withdrawal payout. -/
theorem outA_coalitionCharge {o : Nat} (victim : Adr)
    (steps : List (ProrataAccountingStep o)) :
    outA victim coalitionCharge steps = (steps.map (stepPayout victim)).sum := rfl

/-! ## The SF-frozen attack trace -/

/-- The open diagnostic attack trace of SF §5's P4 subsection.

`coalition` is the finite attacker coalition, `victim` is the designated victim
outside it, and the trace begins at the PRORATA deployment root: `realizes`
carries the whole realized accounting history, so every settled supply or
target-balance movement in it is classified by exactly one step.

`schedule` is the frozen strategy/accounting closure on the victim's own moves;
`coalition_covers` designates every other named economic actor as a member of
the coalition.  `charge` splits the remaining credit between the coalition and
the diagnostic outside context, which is what makes the open subsidy statement
available; the closed trace below is this carrier at the closed charge.

Nothing here constrains callee behaviour.  There is no honesty premise, no
cooperation premise, and no no-donation premise: a donation is an ordinary
positive target credit, and the closure only records whose account it is
charged to. -/
structure ProrataOpenAttackTrace {cfg : ChainConfig} {deployed : BlockChain}
    {ca : Adr} (root : DeploymentRoot cfg deployed ca)
    (coalition : Finset Adr) (victim : Adr)
    (charge : ProrataAccountingStep offset.toNat → AttackAttribution)
    (steps : List (ProrataAccountingStep offset.toNat))
    (future : BlockChain) : Prop where
  realizes : ProrataTraceRealizes root steps future
  victim_not_mem : victim ∉ coalition
  coalition_covers : ∀ step ∈ steps, ∀ x : Adr,
    step.provenance.actor = some x → x ≠ victim → x ∈ coalition
  schedule : VictimSchedule victim steps

/-- The SF-frozen closed attack trace: the open carrier at the closed charge,
where every non-victim credit — receive-path, forced and native alike — is the
coalition's. -/
abbrev ProrataAttackTrace {cfg : ChainConfig} {deployed : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg deployed ca)
    (coalition : Finset Adr) (victim : Adr)
    (steps : List (ProrataAccountingStep offset.toNat))
    (future : BlockChain) : Prop :=
  ProrataOpenAttackTrace root coalition victim coalitionCharge steps future

/-! ## The adapter: a realized trace is an actor path -/

/-- A realized step moves the share ledger by exactly what it moves total
supply, so the ledger total tracks supply along the whole replay.  This is the
fact the frozen carrier does not state and the actor overlay cannot do
without: it is what turns "the withdrawing actor's own row covers the burn"
into "the rest of the ledger still fits under supply". -/
theorem ledgerSum_of_step {o : Nat} {step : ProrataAccountingStep o}
    {pre mid : RealizedSnapshot}
    (pre_eq : step.pre = pre.snapshot) (post_eq : step.post = mid.snapshot)
    (move : LedgerMove step.kind step.provenance.actor pre.ledger mid.ledger)
    (hledger : sum pre.ledger = pre.snapshot.supply) :
    sum mid.ledger = mid.snapshot.supply := by
  have heff : ProrataAccountingEffect o pre.snapshot step.kind mid.snapshot := by
    rw [← pre_eq, ← post_eq]; exact step.effect
  cases hkind : step.kind with
  | deposit amount minted =>
      rw [hkind] at heff move
      obtain ⟨-, hpost⟩ := heff.deposit_inv
      obtain ⟨x, -, hrow, hrest⟩ := move
      have hsum := sum_eq_add_of_row_add hrow hrest
      have hsupply : mid.snapshot.supply = pre.snapshot.supply + minted := by rw [hpost]
      omega
  | withdraw shares paid =>
      rw [hkind] at heff move
      obtain ⟨-, -, hpost⟩ := heff.withdraw_inv
      obtain ⟨x, -, hcover, hrow, hrest⟩ := move
      have hsum := sum_eq_sub_of_row_sub hcover hrow hrest
      have hsupply : mid.snapshot.supply = pre.snapshot.supply - shares := by rw [hpost]
      omega
  | externalCredit amount =>
      rw [hkind] at heff move
      obtain ⟨-, hpost⟩ := heff.externalCredit_inv
      have hmove : mid.ledger = pre.ledger := move
      rw [hpost, hmove]
      exact hledger
  | silent =>
      rw [hkind] at heff move
      have hpost := heff.silent_inv
      have hmove : mid.ledger = pre.ledger := move
      rw [hpost, hmove]
      exact hledger

/-- One realized step is one actor-classified step.

Every one of the six actor classes is discharged from what the realized carrier
already records: the pricing facts come from the step's own accounting effect,
the per-row movements from its `LedgerMove`, the unique-deposit and full-exit
chronology from the frozen schedule, and the coalition withdrawal's share
sufficiency from the ledger identity above.  No premise is added. -/
private theorem attackStep_of_realized
    {victim : Adr}
    (charge : ProrataAccountingStep offset.toNat → AttackAttribution)
    {step : ProrataAccountingStep offset.toNat}
    {rest : List (ProrataAccountingStep offset.toNat)}
    {pre mid : RealizedSnapshot}
    {state : ProrataAttackState offset.toNat}
    (pre_eq : step.pre = pre.snapshot) (post_eq : step.post = mid.snapshot)
    (move : LedgerMove step.kind step.provenance.actor pre.ledger mid.ledger)
    (hacc : state.accounting = pre.snapshot)
    (hvictim : state.victimShares = (pre.ledger victim).toNat)
    (hledger : sum pre.ledger = pre.snapshot.supply)
    (hprice : PriceLe offset.toNat ⟨0, 0⟩ pre.snapshot)
    (hpart : state.SharesPartition)
    (hcons : state.VictimConsistent)
    (hadmits : state.phase.Admits victim (step :: rest)) :
    ∃ (kind : ProrataAttackKind) (post : ProrataAttackState offset.toNat),
      ProrataAttackEffect offset.toNat state kind post ∧
        post.accounting = mid.snapshot ∧
        post.victimShares = (mid.ledger victim).toNat ∧
        post.phase.Admits victim rest ∧
        post.inA = state.inA + (charge step).coalitionAmount (stepCredit victim step) ∧
        post.outA = state.outA + (charge step).coalitionAmount (stepPayout victim step) ∧
        post.outsideSubsidy =
          state.outsideSubsidy + (charge step).outsideAmount (stepCredit victim step) := by
  have heff : ProrataAccountingEffect offset.toNat pre.snapshot step.kind mid.snapshot := by
    rw [← pre_eq, ← post_eq]; exact step.effect
  by_cases hactor : step.provenance.actor = some victim
  · -- The victim's own step.
    have hcredit : stepCredit victim step = 0 := by simp [stepCredit, hactor]
    have hpayout : stepPayout victim step = 0 := by simp [stepPayout, hactor]
    cases hkind : step.kind with
    | deposit amount minted =>
        rw [hkind] at heff move
        have hmoves := victimMoves_cons_of_move (steps := rest) hactor
          (by rw [hkind]; exact fun h => ProrataAccountingKind.noConfusion h)
        obtain ⟨hphase, hrem⟩ := victimDeposit_phase hadmits hmoves hkind
        obtain ⟨hquote, hpost⟩ := heff.deposit_inv
        have hminted : minted = mintN offset.toNat amount
            state.accounting.supply state.accounting.balance := by rw [hacc]; exact hquote
        have hbacked : state.accounting.supply ≤
            offset.toNat * state.accounting.balance := by
          rw [hacc]; exact backed_of_priceLe_genesis hprice
        refine ⟨_, _, ProrataAttackEffect.victimDeposit state amount minted
          hphase hminted hbacked, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hacc, hpost]
        · simp only
          rw [hvictim, LedgerMove.deposit_row move hactor]
        · simpa only [VictimPhase.Admits] using hrem
        · simp [hcredit]
        · simp [hpayout]
        · simp [hcredit]
    | withdraw shares paid =>
        rw [hkind] at heff move
        have hmoves := victimMoves_cons_of_move (steps := rest) hactor
          (by rw [hkind]; exact fun h => ProrataAccountingKind.noConfusion h)
        obtain ⟨dep, hphase, hshares, hrem⟩ := victimExit_phase hadmits hmoves hkind
        obtain ⟨-, hquote, hpost⟩ := heff.withdraw_inv
        have hfull : state.victimShares = dep.minted := by
          unfold ProrataAttackState.VictimConsistent at hcons
          rw [hphase] at hcons
          exact hcons.1
        have hpaid : paid = payN offset.toNat dep.minted
            state.accounting.supply state.accounting.balance := by
          rw [hacc, ← hshares]; exact hquote
        refine ⟨_, _, ProrataAttackEffect.victimExit state dep paid
          hphase hfull hpaid, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hacc, hpost, hshares]
        · simp only
          rw [hvictim, LedgerMove.withdraw_row move hactor, hshares]
        · simpa only [VictimPhase.Admits] using hrem
        · simp [hcredit]
        · simp [hpayout]
        · simp [hcredit]
    | externalCredit amount =>
        exact absurd
          (victimCredit_absurd hadmits
            (victimMoves_cons_of_move (steps := rest) hactor
              (by rw [hkind]; exact fun h => ProrataAccountingKind.noConfusion h))
            hkind)
          not_false
    | silent =>
        rw [hkind] at heff move
        have hmoves : victimMoves victim rest = victimMoves victim (step :: rest) :=
          (victimMoves_cons_of_silent hkind).symm
        have hpost := heff.silent_inv
        have hmove : mid.ledger = pre.ledger := move
        refine ⟨_, _, ProrataAttackEffect.silent state, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hacc, ← hpost]
        · rw [hmove, hvictim]
        · exact hadmits.of_moves_eq hmoves
        · simp [hcredit]
        · simp [hpayout]
        · simp [hcredit]
  · -- A step of some actor other than the victim.
    have hrow : mid.ledger victim = pre.ledger victim :=
      LedgerMove.eq_of_ne_actor move hactor
    have hadmits' : state.phase.Admits victim rest :=
      hadmits.of_moves_eq (victimMoves_cons_of_foreign hactor).symm
    cases hkind : step.kind with
    | deposit amount minted =>
        rw [hkind] at heff move
        obtain ⟨hquote, hpost⟩ := heff.deposit_inv
        have hminted : minted = mintN offset.toNat amount
            state.accounting.supply state.accounting.balance := by rw [hacc]; exact hquote
        refine ⟨_, _, ProrataAttackEffect.nonVictimDeposit state (charge step)
          amount minted hminted, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hacc, hpost]
        · simp only
          rw [hvictim, hrow]
        · exact hadmits'
        · simp [stepCredit, hactor, hkind]
        · simp [stepPayout, hactor, hkind]
        · simp [stepCredit, hactor, hkind]
    | withdraw shares paid =>
        rw [hkind] at heff move
        obtain ⟨-, hquote, hpost⟩ := heff.withdraw_inv
        obtain ⟨x, hx, hcover, -, -⟩ := move
        have hne : x ≠ victim := by
          intro hc; exact hactor (hx.trans (congrArg some hc))
        have hbound := add_le_sum_of_ne pre.ledger hne
        have hshares : shares ≤ state.nonVictimShares := by
          unfold ProrataAttackState.SharesPartition at hpart
          rw [hacc] at hpart
          omega
        have hpaid : paid = payN offset.toNat shares
            state.accounting.supply state.accounting.balance := by rw [hacc]; exact hquote
        refine ⟨_, _, ProrataAttackEffect.nonVictimWithdraw state (charge step)
          shares paid hshares hpaid, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hacc, hpost]
        · simp only
          rw [hvictim, hrow]
        · exact hadmits'
        · simp [stepCredit, hactor, hkind]
        · simp [stepPayout, hactor, hkind]
        · simp [stepCredit, hactor, hkind]
    | externalCredit amount =>
        rw [hkind] at heff move
        obtain ⟨hpositive, hpost⟩ := heff.externalCredit_inv
        refine ⟨_, _, ProrataAttackEffect.externalCredit state (charge step)
          amount hpositive, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [hacc, hpost]
        · simp only
          rw [hvictim, hrow]
        · exact hadmits'
        · simp [stepCredit, hactor, hkind]
        · simp [stepPayout, hactor, hkind]
        · simp [stepCredit, hactor, hkind]
    | silent =>
        rw [hkind] at heff move
        have hpost := heff.silent_inv
        have hmove : mid.ledger = pre.ledger := move
        refine ⟨_, _, ProrataAttackEffect.silent state, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hacc, ← hpost]
        · rw [hmove, hvictim]
        · exact hadmits'
        · simp [stepCredit, hactor, hkind]
        · simp [stepPayout, hactor, hkind]
        · simp [stepCredit, hactor, hkind]

/-- The fold: a realized replay extends an actor path by exactly its own steps,
carrying the coalition accounting along.  The replay is `cons`-shaped from an
arbitrary boundary and the path is `snoc`-shaped from genesis, so the coupling
invariants — accounting projection, the victim's own ledger row, the ledger
total, the genesis price anchor and the remaining victim schedule — travel
forward one step at a time. -/
private theorem exists_attackPath_of_replay
    {victim : Adr}
    (charge : ProrataAccountingStep offset.toNat → AttackAttribution)
    {first last : RealizedSnapshot}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (replay : ProrataAccountingReplay offset.toNat first steps last) :
    ∀ state : ProrataAttackState offset.toNat,
      ProrataAttackPath offset.toNat state →
      state.accounting = first.snapshot →
      state.victimShares = (first.ledger victim).toNat →
      sum first.ledger = first.snapshot.supply →
      PriceLe offset.toNat ⟨0, 0⟩ first.snapshot →
      state.phase.Admits victim steps →
      ∃ final : ProrataAttackState offset.toNat,
        ProrataAttackPath offset.toNat final ∧
          final.inA = state.inA + inA victim charge steps ∧
          final.outA = state.outA + outA victim charge steps ∧
          final.outsideSubsidy =
            state.outsideSubsidy + outsideSubsidy victim charge steps := by
  induction replay with
  | nil boundary =>
      intro state path _ _ _ _ _
      exact ⟨state, path, by simp [inA], by simp [outA], by simp [outsideSubsidy]⟩
  | @cons pre mid last hd tl pre_eq post_eq move tail ih =>
      intro state path hacc hvictim hledger hprice hadmits
      have hstruct := path.structuralInvariant offset_ne_zero
      obtain ⟨kind, next, effect, hacc', hvictim', hadmits', hin, hout, hsub⟩ :=
        attackStep_of_realized charge pre_eq post_eq move hacc hvictim hledger hprice
          hstruct.1 hstruct.2.2 hadmits
      have path' : ProrataAttackPath offset.toNat next :=
        ProrataAttackPath.snoc ⟨state, next, kind, hd.provenance, effect⟩ path
      have hledger' : sum mid.ledger = mid.snapshot.supply :=
        ledgerSum_of_step pre_eq post_eq move hledger
      have hprice' : PriceLe offset.toNat ⟨0, 0⟩ mid.snapshot := by
        refine PriceLe.trans offset_ne_zero hprice ?_
        have h := ProrataAccountingEffect.priceLe offset_ne_zero hd.effect
        rwa [pre_eq, post_eq] at h
      obtain ⟨final, hfinal, h1, h2, h3⟩ :=
        ih next path' hacc' hvictim' hledger' hprice' hadmits'
      refine ⟨final, hfinal, ?_, ?_, ?_⟩
      · rw [h1, hin]; simp [inA]; omega
      · rw [h2, hout]; simp [outA]; omega
      · rw [h3, hsub]; simp [outsideSubsidy]; omega

/-- The adapter of SF §5's P4 subsection: every attack trace over the realized
history is an actor path from the deployment genesis whose coalition
accounting is exactly the trace's own.

The genesis conditions are read off the deployment root: empty PRORATA storage
gives the zero accounting snapshot, the zero victim row and the ledger
identity, and the zero snapshot is its own price anchor. -/
theorem exists_attackPath {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {coalition : Finset Adr} {victim : Adr}
    {charge : ProrataAccountingStep offset.toNat → AttackAttribution}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (trace : ProrataOpenAttackTrace root coalition victim charge steps future) :
    ∃ final : ProrataAttackState offset.toNat,
      ProrataAttackPath offset.toNat final ∧
        final.inA = inA victim charge steps ∧
        final.outA = outA victim charge steps ∧
        final.outsideSubsidy = outsideSubsidy victim charge steps := by
  have hsnapshot : (RealizedSnapshot.ofState ca deployed.state).snapshot = ⟨0, 0⟩ := by
    rw [RealizedSnapshot.snapshot_ofState, root.accountingSnapshot]
  have hledger : sum (RealizedSnapshot.ofState ca deployed.state).ledger =
      (RealizedSnapshot.ofState ca deployed.state).snapshot.supply := by
    show balSum (deployed.state.getStor ca) = supplyN (deployed.state.getStor ca)
    rw [root.emptyStorage]
    exact Inv.of_empty.1
  have hrow : (0 : Nat) = ((RealizedSnapshot.ofState ca deployed.state).ledger victim).toNat := by
    show (0 : Nat) = (Stor.rest (deployed.state.getStor ca) victim).toNat
    rw [root.emptyStorage, show Stor.rest Stor.empty victim = (0 : B256) from rfl,
      B256.toNat_zero]
  obtain ⟨final, hfinal, h1, h2, h3⟩ :=
    exists_attackPath_of_replay charge trace.realizes.toAccountingReplay
      (ProrataAttackState.genesis offset.toNat) .genesis
      hsnapshot.symm hrow hledger
      (by rw [hsnapshot]; exact PriceLe.refl offset.toNat ⟨0, 0⟩)
      trace.schedule
  exact ⟨final, hfinal, by simpa [ProrataAttackState.genesis] using h1,
    by simpa [ProrataAttackState.genesis] using h2,
    by simpa [ProrataAttackState.genesis] using h3⟩

/-! ## The SF-frozen P4 headlines -/

/-- **`attacker_open_context`** (SF §5, P4).  For diagnostic use over an open
trace: the coalition's settled take is bounded by its own settled input plus
the outside subsidy it was handed.

`outsideSubsidy` is exactly the settled positive credit charged to neither the
coalition nor the designated victim deposit — receive-path, forced, native and
protocol credit alike.  The `2 ≤ O` premise of the pure result is discharged
by the compiled offset. -/
theorem attacker_open_context {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {coalition : Finset Adr} {victim : Adr}
    {charge : ProrataAccountingStep offset.toNat → AttackAttribution}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (trace : ProrataOpenAttackTrace root coalition victim charge steps future) :
    outA victim charge steps ≤
      inA victim charge steps + outsideSubsidy victim charge steps := by
  obtain ⟨final, path, h1, h2, h3⟩ := exists_attackPath trace
  have h := path.attacker_open_context_of_attackPath two_le_offset
  omega

/-- **`attacker_no_profit`** (SF §5, P4).  No closed attack trace is profitable:
whatever the coalition takes out of PRORATA it has already put in.

The trace is a strategy/accounting closure, not an honesty premise.  Callee
code is arbitrary: reentrancy, donations, forced and native credit, and every
ordering the realized carrier admits are all inside the quantifier.  The
necessary `2 ≤ O` premise is discharged by the compiled offset `O = 1000`. -/
theorem attacker_no_profit {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {coalition : Finset Adr} {victim : Adr}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (trace : ProrataAttackTrace root coalition victim steps future) :
    outA victim coalitionCharge steps ≤ inA victim coalitionCharge steps := by
  have h := attacker_open_context trace
  rw [outsideSubsidy_coalitionCharge] at h
  omega

/-- **`victim_loss_bound`** (SF §5, P4).  If the victim's successful deposit saw
pre-credit `(Sdep, Bdep)`, deposited `v` and minted `m`, and a later successful
exit burns that unchanged `m` and pays `p`, the victim's shortfall is at most
one virtual-asset quantum above the genesis-anchored price ratio.

The successful-exit premise is the second disjunct of the trace's own frozen
schedule: the contract makes no liveness claim, so no theorem asserts the exit
is available.  The bound is independent of the `2 ≤ O` no-profit boundary. -/
theorem victim_loss_bound {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {coalition : Finset Adr} {victim : Adr}
    {charge : ProrataAccountingStep offset.toNat → AttackAttribution}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (trace : ProrataOpenAttackTrace root coalition victim charge steps future)
    {deposit exit : ProrataAccountingStep offset.toNat} {v m p : Nat}
    (hmoves : victimMoves victim steps = [deposit, exit])
    (hdeposit : deposit.kind = .deposit v m)
    (hexit : exit.kind = .withdraw m p) :
    v - p ≤ Nat.div (deposit.pre.balance + 1) (deposit.pre.supply + offset.toNat) + 1 := by
  have replay := trace.realizes.toAccountingReplay
  have hd := deposit.effect
  rw [hdeposit] at hd
  obtain ⟨hquote, hpost⟩ := hd.deposit_inv
  have hw := exit.effect
  rw [hexit] at hw
  obtain ⟨-, hpaid, -⟩ := hw.withdraw_inv
  have hprice : PriceLe offset.toNat deposit.post exit.pre :=
    replay.priceLe_of_filter_pair offset_ne_zero hmoves
  rw [hpost] at hprice
  exact victim_loss_le_div_add_one offset_ne_zero hquote hprice hpaid

end Prorata

end Blanc
