import Blanc.ExecutionAccountingReplay

namespace Blanc.ExecutionAccountingReplay

open Jaune

/-- Signed entry boundaries retain exact message values even at arbitrary raw roots. -/
def signedBalanceEntry (ca : Adr) (sevm : Sevm) (state : State) : Int :=
  if sevm.currentTarget = ca then
    (state.bal ca).toNat - (sevm.value.toNat : Int)
  else (state.bal ca).toNat

theorem signedBalanceEntry_eq_ofState {ca : Adr} {msg : Msg} {entry : Benv}
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false → msg.currentTarget = ca → msg.value = 0)
    (transfer : msg.benvAfterTransfer = .ok entry)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256) :
    signedBalanceEntry ca (initSevm (msg.withBenv entry)) entry.state =
      ((msg.benv.state.bal ca).toNat : Int) := by
  change (if msg.currentTarget = ca then
    ((entry.state.bal ca).toNat : Int) - (msg.value.toNat : Int)
    else ((entry.state.bal ca).toNat : Int)) = _
  cases transfers : msg.shouldTransferValue with
  | false =>
    have noTransfer : ¬ msg.shouldTransferValue = true := by
      rw [transfers]
      decide
    rw [of_benvAfterTransfer_no noTransfer transfer]
    by_cases target : msg.currentTarget = ca
    · rw [ite_eq_left target, value_zero transfers target]
      change ((msg.benv.state.bal ca).toNat : Int) - 0 = _
      exact sub_zero _
    · rw [ite_eq_right target]
  | true =>
    obtain ⟨debit, sub, rfl⟩ := of_benvAfterTransfer transfers transfer
    by_cases target : msg.currentTarget = ca
    · subst ca
      rw [ite_eq_left rfl]
      change (((debit.addBal msg.currentTarget msg.value).bal msg.currentTarget).toNat : Int)
        - (msg.value.toNat : Int) = _
      rw [of_transfer_bal_target sub (caller_ne transfers) sum_nof, Int.natCast_add]
      omega
    · rw [ite_eq_right target]
      change (((debit.addBal msg.currentTarget msg.value).bal ca).toNat : Int) = _
      rw [of_transfer_bal_other sub (caller_ne transfers) target]

/-- Message-value credits and unobserved incidental credits have distinct constructors. -/
inductive SignedBalanceCredit where
  | message (frame : Exec.Frame)
  | incidental (amount : Nat)

def SignedBalanceCredit.amount : SignedBalanceCredit → Nat
  | .message frame => frame.sevm.value.toNat
  | .incidental amount => amount

/-- Incidental credits retain no execution frame. -/
def SignedBalanceCredit.frames : SignedBalanceCredit → List Exec.Frame
  | .message frame => [frame]
  | .incidental _ => []

theorem signedBalanceCredit_frames_sum_le (steps : List SignedBalanceCredit) :
    ((steps.flatMap SignedBalanceCredit.frames).map
      (fun frame => frame.sevm.value.toNat)).sum ≤
      (steps.map SignedBalanceCredit.amount).sum := by
  induction steps with
  | nil => exact Nat.le_refl 0
  | cons credit rest ih =>
    cases credit with
    | message frame =>
      simp only [List.flatMap_cons, SignedBalanceCredit.frames, List.singleton_append,
        List.map_cons, List.sum_cons, SignedBalanceCredit.amount]
      omega
    | incidental amount =>
      simp only [List.flatMap_cons, SignedBalanceCredit.frames, List.nil_append,
        List.map_cons, List.sum_cons, SignedBalanceCredit.amount]
      omega

def signedBalanceCarrier (ca : Adr) : ReplayCarrier ca where
  Snap := Int
  Step := SignedBalanceCredit
  Tag := Unit
  Replay pre steps post := pre + ((steps.map SignedBalanceCredit.amount).sum : Int) = post
  ofState state := (state.bal ca).toNat
  frameEntry := signedBalanceEntry ca
  nil := by
    intro boundary
    simp only [List.map_nil, List.sum_nil, Int.ofNat_zero, add_zero]
  silent := by
    intro _ _ _ balance
    exact congrArg Int.ofNat balance
  credit := by
    intro _ pre post amount _ balance _
    refine ⟨[.incidental amount], ?_⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SignedBalanceCredit.amount, Nat.add_zero]
    rw [balance, Int.natCast_add]
  entry_eq_ofState := signedBalanceEntry_eq_ofState

theorem signedBalanceCarrier_append {ca : Adr} {pre mid post : Int}
    {left right : List SignedBalanceCredit}
    (first : (signedBalanceCarrier ca).Replay pre left mid)
    (second : (signedBalanceCarrier ca).Replay mid right post) :
    (signedBalanceCarrier ca).Replay pre (left ++ right) post := by
  change pre + (((left ++ right).map SignedBalanceCredit.amount).sum : Int) = post
  rw [List.map_append, List.sum_append, Int.natCast_add]
  change pre + ((left.map SignedBalanceCredit.amount).sum : Int) = mid at first
  change mid + ((right.map SignedBalanceCredit.amount).sum : Int) = post at second
  omega

end Blanc.ExecutionAccountingReplay
