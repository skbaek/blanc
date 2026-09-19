import Blanc.DripAccounting

namespace Blanc.Drip

open Jaune

def Kind.isCall : Kind → Bool
  | .drip _ => true
  | .join _ _ _ _ _ => true
  | .exit _ _ _ _ _ => true
  | .externalCredit _ => false
  | .silent => false

/-- The call projection of a ledger, in ledger order. -/
def callKinds {scale : Nat} {fresh : Nat → Nat → Nat}
    (steps : List (Step scale fresh)) : List Kind :=
  (steps.map Step.kind).filter Kind.isCall

@[simp] theorem callKinds_nil {scale : Nat} {fresh : Nat → Nat → Nat} :
    callKinds ([] : List (Step scale fresh)) = [] := rfl
theorem callKinds_append {scale : Nat} {fresh : Nat → Nat → Nat}
    (left right : List (Step scale fresh)) :
    callKinds (left ++ right) = callKinds left ++ callKinds right := by
  simp [callKinds]

def Kind.advance (scale : Nat) (fresh : Nat → Nat → Nat) (chi cu : Nat) :
    Kind → Nat × Nat
  | .drip elapsed => (fresh chi elapsed, cu)
  | .join true _ _ units elapsed => (fresh chi elapsed, cu + units)
  | .join false _ _ _ elapsed => (fresh chi elapsed, cu)
  | .exit true _ units _ elapsed => (fresh chi elapsed, cu - units)
  | .exit false _ _ _ elapsed => (fresh chi elapsed, cu)
  | .externalCredit _ => (chi, cu)
  | .silent => (chi, cu)

structure CallTally where
  accrual : Nat
  joined : Nat
  joinResidue : Nat
  paid : Nat
  exitResidue : Nat
  allJoined : Nat
  allPaid : Nat

def CallTally.zero : CallTally := ⟨0, 0, 0, 0, 0, 0, 0⟩

def CallTally.add (a b : CallTally) : CallTally :=
  ⟨a.accrual + b.accrual, a.joined + b.joined, a.joinResidue + b.joinResidue,
    a.paid + b.paid, a.exitResidue + b.exitResidue, a.allJoined + b.allJoined,
    a.allPaid + b.allPaid⟩

def Kind.callTally (scale : Nat) (fresh : Nat → Nat → Nat) (chi cu : Nat) :
    Kind → CallTally
  | .drip elapsed => ⟨cu * (fresh chi elapsed - chi), 0, 0, 0, 0, 0, 0⟩
  | .join true _ assets _ elapsed =>
      ⟨cu * (fresh chi elapsed - chi), assets,
        joinResidueOf scale assets (fresh chi elapsed), 0, 0, assets, 0⟩
  | .join false _ assets _ elapsed =>
      ⟨cu * (fresh chi elapsed - chi), 0, 0, 0, 0, assets, 0⟩
  | .exit true _ units payout elapsed =>
      ⟨cu * (fresh chi elapsed - chi), 0, 0, payout,
        exitResidueOf scale units (fresh chi elapsed), 0, payout⟩
  | .exit false _ _ payout elapsed =>
      ⟨cu * (fresh chi elapsed - chi), 0, 0, 0, 0, 0, payout⟩
  | .externalCredit _ => CallTally.zero
  | .silent => CallTally.zero

def transcriptTally (scale : Nat) (fresh : Nat → Nat → Nat) :
    Nat → Nat → List Kind → CallTally
  | _, _, [] => CallTally.zero
  | chi, cu, kind :: rest =>
      (kind.callTally scale fresh chi cu).add
        (transcriptTally scale fresh (kind.advance scale fresh chi cu).1
          (kind.advance scale fresh chi cu).2 rest)

def transcriptState (scale : Nat) (fresh : Nat → Nat → Nat) :
    Nat → Nat → List Kind → Nat × Nat
  | chi, cu, [] => (chi, cu)
  | chi, cu, kind :: rest =>
      transcriptState scale fresh (kind.advance scale fresh chi cu).1
        (kind.advance scale fresh chi cu).2 rest

/-- Every ledger sum except `giftSum` is a function of the call projection. -/
theorem Chain.transcriptTally_eq {scale : Nat} {fresh : Nat → Nat → Nat}
    {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t) :
    transcriptTally scale fresh s.chi s.coalitionUnits (callKinds steps) =
      ⟨Chain.accrualSum steps, Chain.joinedSum steps, Chain.joinResidueSum steps,
        Chain.paidSum steps, Chain.exitResidueSum steps,
        Chain.allJoinedSum steps, Chain.allPaidSum steps⟩ := by
  induction chain with
  | nil s => simp [callKinds, transcriptTally, CallTally.zero]
  | cons entry tail ih =>
      rename_i s t step rest
      subst s
      rcases step with ⟨pre, kind, post, effect⟩
      cases effect <;>
        simp_all [callKinds, Kind.isCall, transcriptTally, Kind.callTally, Kind.advance,
          CallTally.add, Step.accrual, Step.joined, Step.joinResidue,
          Step.paid, Step.exitResidue, Step.allJoined, Step.allPaid,
          Chain.accrualSum, Chain.joinedSum, Chain.joinResidueSum,
          Chain.paidSum, Chain.exitResidueSum, Chain.allJoinedSum,
          Chain.allPaidSum]

theorem Chain.transcriptState_eq {scale : Nat} {fresh : Nat → Nat → Nat}
    {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t) :
    transcriptState scale fresh s.chi s.coalitionUnits (callKinds steps) =
      (t.chi, t.coalitionUnits) := by
  induction chain with
  | nil s => rfl
  | cons entry tail ih =>
      rename_i s t step rest
      subst s
      rcases step with ⟨pre, kind, post, effect⟩
      cases effect <;>
        simp_all [callKinds, Kind.isCall, transcriptState, Kind.advance]

/-- Non-call steps never move the total supply. -/
theorem Chain.totalUnits_eq_of_callKinds_nil {scale : Nat}
    {fresh : Nat → Nat → Nat} {s t : Snapshot} {steps : List (Step scale fresh)}
    (chain : Chain scale fresh s steps t) (none : callKinds steps = []) :
    t.totalUnits = s.totalUnits := by
  induction chain with
  | nil s => rfl
  | cons entry tail ih =>
      rename_i s t step rest
      subst s
      rcases step with ⟨pre, kind, post, effect⟩
      cases effect with
      | drip => simp [callKinds, Kind.isCall] at none
      | joinCounted => simp [callKinds, Kind.isCall] at none
      | joinOutside => simp [callKinds, Kind.isCall] at none
      | exitCounted => simp [callKinds, Kind.isCall] at none
      | exitOutside => simp [callKinds, Kind.isCall] at none
      | externalCredit =>
          have hnone : callKinds rest = [] := by
            simpa [callKinds, Kind.isCall] using none
          simpa using ih hnone
      | silent =>
          have hnone : callKinds rest = [] := by
            simpa [callKinds, Kind.isCall] using none
          simpa using ih hnone

theorem transcriptState_drips (chi cu : Nat) (ks : List Nat) :
    (transcriptState scale.toNat freshNat chi cu (ks.map Kind.drip)).1 =
      segmentIndex scale.toNat half.toNat rate.toNat chi ks := by
  induction ks generalizing chi cu with
  | nil => rfl
  | cons elapsed rest ih =>
      change
        (transcriptState scale.toNat freshNat (freshNat chi elapsed) cu
          (rest.map Kind.drip)).1 =
          segmentIndexFrom scale.toNat half.toNat rate.toNat
            (freshNat chi elapsed) rest
      simpa [segmentIndex] using ih (freshNat chi elapsed) cu

end Blanc.Drip
