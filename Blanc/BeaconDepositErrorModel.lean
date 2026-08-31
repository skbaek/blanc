import Blanc.BeaconDepositCorrectness
import Blanc.BeaconDepositErrorCatalog

/-!
# Beacon deposit reachable model-error partition

This module records the exact first-failing source guard represented by each
compiled error auxiliary.  The terminal `assert_false` constructor is excluded
by the pure-model theorem and therefore has no catalogue row.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-- Exact source-order premises for one reachable deposit failure. -/
def DepositFailureSpec
    (H : Bytes → B256) (state : Acc)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (value : Nat) : ReachableReason → Prop
  | .pubkeyLength =>
      pubkey.length ≠ 48
  | .withdrawalCredentialsLength =>
      pubkey.length = 48 ∧ withdrawalCredentials.length ≠ 32
  | .signatureLength =>
      pubkey.length = 48 ∧ withdrawalCredentials.length = 32 ∧
        signature.length ≠ 96
  | .valueTooLow =>
      pubkey.length = 48 ∧ withdrawalCredentials.length = 32 ∧
        signature.length = 96 ∧ value < oneEther
  | .valueNotGweiMultiple =>
      pubkey.length = 48 ∧ withdrawalCredentials.length = 32 ∧
        signature.length = 96 ∧ oneEther ≤ value ∧ value % oneGwei ≠ 0
  | .valueTooHigh =>
      pubkey.length = 48 ∧ withdrawalCredentials.length = 32 ∧
        signature.length = 96 ∧ oneEther ≤ value ∧ value % oneGwei = 0 ∧
        2 ^ 64 - 1 < value / oneGwei
  | .depositDataRootMismatch =>
      pubkey.length = 48 ∧ withdrawalCredentials.length = 32 ∧
        signature.length = 96 ∧ oneEther ≤ value ∧ value % oneGwei = 0 ∧
        value / oneGwei ≤ 2 ^ 64 - 1 ∧
        depositDataNode H pubkey withdrawalCredentials signature
          (le64 (value / oneGwei)) ≠ depositDataRoot
  | .merkleTreeFull =>
      pubkey.length = 48 ∧ withdrawalCredentials.length = 32 ∧
        signature.length = 96 ∧ oneEther ≤ value ∧ value % oneGwei = 0 ∧
        value / oneGwei ≤ 2 ^ 64 - 1 ∧
        depositDataNode H pubkey withdrawalCredentials signature
          (le64 (value / oneGwei)) = depositDataRoot ∧
        ¬ state.count < 2 ^ 32 - 1

private theorem deposit_pubkeyLength_error_spec
    {H : Bytes → B256} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {value : Nat}
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error .pubkey_length) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value .pubkeyLength := by
  simp only [deposit] at herror
  split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror
  all_goals simp_all [DepositFailureSpec]

private theorem deposit_withdrawalCredentialsLength_error_spec
    {H : Bytes → B256} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {value : Nat}
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error .withdrawal_credentials_length) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value .withdrawalCredentialsLength := by
  simp only [deposit] at herror
  split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror
  all_goals simp_all [DepositFailureSpec]

private theorem deposit_signatureLength_error_spec
    {H : Bytes → B256} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {value : Nat}
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error .signature_length) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value .signatureLength := by
  simp only [deposit] at herror
  split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror
  all_goals simp_all [DepositFailureSpec]

private theorem deposit_valueTooLow_error_spec
    {H : Bytes → B256} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {value : Nat}
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error .value_too_low) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value .valueTooLow := by
  simp only [deposit] at herror
  split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror
  all_goals simp_all [DepositFailureSpec]

private theorem deposit_valueNotGweiMultiple_error_spec
    {H : Bytes → B256} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {value : Nat}
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error .value_not_gwei_multiple) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value .valueNotGweiMultiple := by
  simp only [deposit] at herror
  split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror
  all_goals simp_all [DepositFailureSpec]

private theorem deposit_valueTooHigh_error_spec
    {H : Bytes → B256} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {value : Nat}
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error .value_too_high) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value .valueTooHigh := by
  simp only [deposit] at herror
  split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror
  all_goals simp_all [DepositFailureSpec]

private theorem deposit_depositDataRootMismatch_error_spec
    {H : Bytes → B256} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {value : Nat}
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error .deposit_data_root_mismatch) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value .depositDataRootMismatch := by
  simp only [deposit] at herror
  split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror
  all_goals simp_all [DepositFailureSpec]

private theorem deposit_merkleTreeFull_error_spec
    {H : Bytes → B256} {state : Acc}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {value : Nat}
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error .merkle_tree_full) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value .merkleTreeFull := by
  simp only [deposit] at herror
  split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror <;>
    try split at herror <;> try split at herror <;> try split at herror
  all_goals simp_all [DepositFailureSpec]

/-- A model error at a catalogued reason exposes exactly the first-failing
guard premises for that row. -/
theorem deposit_error_spec
    (H : Bytes → B256) (state : Acc)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (value : Nat) (error : ReachableReason)
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error error.reason) :
    DepositFailureSpec H state pubkey withdrawalCredentials signature
      depositDataRoot value error := by
  cases error with
  | pubkeyLength => exact deposit_pubkeyLength_error_spec herror
  | withdrawalCredentialsLength =>
      exact deposit_withdrawalCredentialsLength_error_spec herror
  | signatureLength => exact deposit_signatureLength_error_spec herror
  | valueTooLow => exact deposit_valueTooLow_error_spec herror
  | valueNotGweiMultiple =>
      exact deposit_valueNotGweiMultiple_error_spec herror
  | valueTooHigh => exact deposit_valueTooHigh_error_spec herror
  | depositDataRootMismatch =>
      exact deposit_depositDataRootMismatch_error_spec herror
  | merkleTreeFull => exact deposit_merkleTreeFull_error_spec herror

/-- Every model error is represented by the eight-row compiled catalogue;
the only other source-model label is ruled out by `deposit_ne_assert_false`. -/
theorem deposit_error_reachable
    (H : Bytes → B256) (state : Acc)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (value : Nat) (reason : Reason)
    (herror : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .error reason) :
    ∃ error : ReachableReason, error.reason = reason := by
  cases reason with
  | pubkey_length => exact ⟨.pubkeyLength, rfl⟩
  | withdrawal_credentials_length =>
      exact ⟨.withdrawalCredentialsLength, rfl⟩
  | signature_length => exact ⟨.signatureLength, rfl⟩
  | value_too_low => exact ⟨.valueTooLow, rfl⟩
  | value_not_gwei_multiple => exact ⟨.valueNotGweiMultiple, rfl⟩
  | value_too_high => exact ⟨.valueTooHigh, rfl⟩
  | deposit_data_root_mismatch => exact ⟨.depositDataRootMismatch, rfl⟩
  | merkle_tree_full => exact ⟨.merkleTreeFull, rfl⟩
  | assert_false =>
      exact (deposit_ne_assert_false H state pubkey withdrawalCredentials
        signature depositDataRoot value herror).elim

/-- Total pure-model partition into success or one exact reachable error row. -/
theorem deposit_ok_or_reachable_error
    (H : Bytes → B256) (state : Acc)
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (value : Nat) :
    (∃ result, deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value = .ok result) ∨
    (∃ error : ReachableReason,
      deposit H state pubkey withdrawalCredentials signature
        depositDataRoot value = .error error.reason ∧
      DepositFailureSpec H state pubkey withdrawalCredentials signature
        depositDataRoot value error) := by
  cases hdeposit : deposit H state pubkey withdrawalCredentials signature
      depositDataRoot value with
  | ok result => exact Or.inl ⟨result, rfl⟩
  | error reason =>
      obtain ⟨error, rfl⟩ := deposit_error_reachable H state pubkey
        withdrawalCredentials signature depositDataRoot value reason hdeposit
      exact Or.inr ⟨error, rfl,
        deposit_error_spec H state pubkey withdrawalCredentials signature
          depositDataRoot value error hdeposit⟩

end Blanc.BeaconDeposit
