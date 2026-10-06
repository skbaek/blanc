import Blanc.Lift.UniswapV2Pair.Properties
import Blanc.Lift.UniswapV2Pair.ModelMutants

/-! Required kernel statement controls on actual reachable typed-model states.
The NoShrink control runs the production driver. The mutant controls run the
arithmetic-parameterised driver of `ModelMutants` (equal to production `runTyped`
at the production record, `runTypedWith_production`) at a goal mutant, on states the
mutant itself reaches. Evidence altitude: typed model, not EVM execution.
-/

namespace Blanc.Lift.UniswapV2Pair.ModelControls

open Jaune

def context : Context :=
  { pair := 17, sender := 20, value := 0, timestamp := 0,
    isStatic := false, invocation := [] }

def answer (value : B256) : ExternalResult :=
  { success := true, returndata := encodeWords [value], codeExists := true,
    recoveryOutput := 0 }

def initialized : State :=
  (runTyped (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
    .done).frame.current.state

def mintTranscript : Transcript :=
  .next (answer 1001) .done (.next (answer 1001) .done (.next (answer 0) .done .done))

def mintRun : RunResult := runTyped initialized context (.mint 20) mintTranscript

def minted : State := mintRun.frame.current.state

def donationTranscript : Transcript :=
  .next (answer 1002) .done (.next (answer 1002) .done .done)

def donationRun : RunResult := runTyped minted context .sync donationTranscript

def checkpoint : State := donationRun.frame.current.state

/-- The witness begins with actual successful factory initialization. -/
theorem initialize_success :
    (runTyped (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
      .done).status = .success [] := by
  rfl


/-- Closed source initialization has exactly the two selected token addresses. -/
theorem initialized_eq : initialized = { State.empty 16 0 with token0 := 18, token1 := 19 } := by
  rfl

/-- The source's checked first-mint price on the required reachable witness. -/
theorem mint_price : mintAmount 1001 1001 0 0 0 = .ok 1 := by
  rw [mintAmount, ite_eq_left rfl]
  have bounded : (1001 : B256).toNat * (1001 : B256).toNat < 2 ^ 256 := by decide
  rw [ite_eq_left bounded]
  have root : Nat.sqrt ((1001 : B256).toNat * (1001 : B256).toNat) = 1001 :=
    Nat.sqrt_eq 1001
  rw [root, ite_eq_left (show 1000 ≤ 1001 by decide)]

def mintExpected : State :=
  { State.empty 16 0 with
    token0 := 18, token1 := 19, totalSupply := 1001,
    balanceOf := Blanc.ledgerCredit (Blanc.ledgerCredit (fun _ => 0) 0 1000) 20 1,
    reserve0 := ⟨1001, by decide⟩, reserve1 := ⟨1001, by decide⟩ }
/-- The witness's first mint executes the real finite source driver. -/
theorem mint_execution : mintRun.status = .success (encodeWords [1]) ∧ minted = mintExpected := by
  have word1001 : Bytes.toB256 (List.take 32 ((1001 : B256).toBytes)) = 1001 := by
    rw [List.take_of_length_le (show (1001 : B256).toBytes.length ≤ 32 from
      Nat.le_of_eq (B256.length_toBytes 1001))]
    exact B256.toB256_toBytes 1001
  have word0 : Bytes.toB256 (List.take 32 ((0 : B256).toBytes)) = 0 := by
    rw [List.take_of_length_le (show (0 : B256).toBytes.length ≤ 32 from
      Nat.le_of_eq (B256.length_toBytes 0))]
    exact B256.toB256_toBytes 0
  have zeroWord : Nat.toB256 0 = 0 := rfl
  have zeroAddress : (0 : B256).toAdr = 0 := rfl
  simp only [minted, mintExpected, mintRun, initialized_eq, mintTranscript, context, answer, runTyped,
    Transcript.work, startTyped, startImmediate, getterResult, State.empty, Frame.enter,
    Frame.lock, Frame.suspend, requestFor, drive, driveTurns, resumeSegment, decodeExternal,
    Frame.beginResume, Frame.withEvents, mintFee, Frame.mintAfterFee, mint_price,
    State.mintLP, State.update, Frame.finishUpdated, Frame.finishLocked, Frame.withUpdate,
    Frame.finish, State.cachedReserves, ne_eq, Nat.le_refl, Nat.zero_le,
    eq_self, not_true_eq_false, Bool.false_eq_true, Bool.not_true,
    Bool.and_false, ite_false, ite_true, encodeWords, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, B256.length_toBytes,
    Fin.val_zero, true_and, B256.sub_zero,
    word1001, word0, zeroWord, zeroAddress]
  exact ⟨rfl, rfl⟩


def checkpointExpected : State :=
  { mintExpected with reserve0 := ⟨1002, by decide⟩, reserve1 := ⟨1002, by decide⟩ }

/-- The ordinary donation is absorbed by an actual successful sync with unchanged LP supply. -/
theorem donation_execution :
    donationRun.status = .success [] ∧ checkpoint = checkpointExpected := by
  rw [checkpoint, donationRun, mint_execution.2]
  exact ⟨rfl, rfl⟩

def shrinkingTranscript : Transcript :=
  .next (answer 0) .done (.next (answer 1002) .done .done)

def shrinkingRun : RunResult := runTyped checkpoint context .sync shrinkingTranscript

def shrunk : State := shrinkingRun.frame.current.state

/-- Removing NoShrink still admits a real sync that stores a zero first reserve. -/
theorem shrinking_execution :
    shrinkingRun.status = .success [] ∧ shrunk = { checkpointExpected with reserve0 := 0 } := by
  rw [shrunk, shrinkingRun, donation_execution.2]
  exact ⟨rfl, rfl⟩

/-- Required kernel counterexample to the fee-off product statement with NoShrink omitted. -/
theorem noShrink_required :
    (runTyped (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
      .done).status = .success [] ∧
    mintRun.status = .success (encodeWords [1]) ∧ donationRun.status = .success [] ∧
    0 < checkpoint.totalSupply.toNat ∧ shrinkingRun.status = .success [] ∧
    ¬ SyncEntryNoShrink checkpoint shrinkingTranscript ∧
    ¬ (checkpoint.reserve0.val * checkpoint.reserve1.val * shrunk.totalSupply.toNat ^ 2 ≤
      shrunk.reserve0.val * shrunk.reserve1.val * checkpoint.totalSupply.toNat ^ 2) := by
  have fails :
      ¬ (checkpoint.reserve0.val * checkpoint.reserve1.val * shrunk.totalSupply.toNat ^ 2 ≤
        shrunk.reserve0.val * shrunk.reserve1.val * checkpoint.totalSupply.toNat ^ 2) := by
    rw [donation_execution.2, shrinking_execution.2]
    decide
  refine ⟨initialize_success, mint_execution.1, donation_execution.1, ?_,
    shrinking_execution.1, ?_, fails⟩
  · rw [donation_execution.2]
    decide
  · intro noShrink
    have zeroWord : shrinkingTranscript.firstWord = 0 := by
      simp only [shrinkingTranscript, Transcript.firstWord, answer, encodeWords,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.take_of_length_le (show (0 : B256).toBytes.length ≤ 32 from
        Nat.le_of_eq (B256.length_toBytes 0))]
      exact B256.toB256_toBytes 0
    have bound := noShrink.1
    rw [donation_execution.2, zeroWord] at bound
    exact (by decide : ¬ 1002 ≤ (0 : B256).toNat) bound

def laterTranscript : Transcript :=
  .next (answer 1004) .done (.next (answer 1004) .done (.next (answer 0) .done .done))

/-! ## Mutated-driver controls -/

section Mutants

open ModelMutants

-- Kernel-decidable run statuses for the evaluated mismatch witnesses below.
deriving instance DecidableEq for RunStatus

/-- The upward mutant keeps the checked first-mint price. -/
theorem up_mint_price : mintRoundUp.mintAmount 1001 1001 0 0 0 = .ok 1 :=
  (mintAmountUp_initial rfl).trans mint_price

/-- Initialization under the upward mutant is production initialization. -/
theorem up_initialize :
    runTypedWith mintRoundUp (State.empty 16 0) { context with sender := 16 } (.initialize 18 19) .done =
      runTyped (State.empty 16 0) { context with sender := 16 } (.initialize 18 19) .done := by
  rfl

def upMintRun : RunResult := runTypedWith mintRoundUp initialized context (.mint 20) mintTranscript

/-- The upward mutant's first mint reaches the production first-mint state. -/
theorem up_mint_execution :
    upMintRun.status = .success (encodeWords [1]) ∧ upMintRun.frame.current.state = mintExpected := by
  have word1001 : Bytes.toB256 (List.take 32 ((1001 : B256).toBytes)) = 1001 := by
    rw [List.take_of_length_le (show (1001 : B256).toBytes.length ≤ 32 from
      Nat.le_of_eq (B256.length_toBytes 1001))]
    exact B256.toB256_toBytes 1001
  have word0 : Bytes.toB256 (List.take 32 ((0 : B256).toBytes)) = 0 := by
    rw [List.take_of_length_le (show (0 : B256).toBytes.length ≤ 32 from
      Nat.le_of_eq (B256.length_toBytes 0))]
    exact B256.toB256_toBytes 0
  have zeroWord : Nat.toB256 0 = 0 := rfl
  have zeroAddress : (0 : B256).toAdr = 0 := rfl
  simp only [upMintRun, mintExpected, initialized_eq, mintTranscript, context, answer, runTypedWith,
    Transcript.work, startTyped, startImmediate, getterResult, State.empty, Frame.enter,
    Frame.lock, Frame.suspend, requestFor, driveWith, driveTurnsWith, resumeWith, resumeSegment,
    decodeExternal, Frame.beginResume, Frame.withEvents, mintFee, Frame.mintAfterFeeWith,
    up_mint_price, State.mintLP, State.update, Frame.finishUpdated, Frame.finishLocked,
    Frame.withUpdate, Frame.finish, State.cachedReserves, ne_eq, Nat.le_refl, Nat.zero_le,
    eq_self, not_true_eq_false, Bool.false_eq_true, Bool.not_true,
    Bool.and_false, ite_false, ite_true, encodeWords, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, B256.length_toBytes,
    Fin.val_zero, true_and, B256.sub_zero,
    word1001, word0, zeroWord, zeroAddress]
  exact ⟨rfl, rfl⟩

def upDonationRun : RunResult :=
  runTypedWith mintRoundUp upMintRun.frame.current.state context .sync donationTranscript

/-- The upward mutant's donation sync reaches the production checkpoint. -/
theorem up_donation_execution :
    upDonationRun.status = .success [] ∧ upDonationRun.frame.current.state = checkpoint := by
  rw [upDonationRun, up_mint_execution.2, donation_execution.2]
  exact ⟨rfl, rfl⟩

def upLaterRun : RunResult := runTypedWith mintRoundUp checkpoint context (.mint 20) laterTranscript

/-- The later mint's feeTo answer is zero, so the fee-off product statement applies. -/
theorem later_feeOff : EntryFeeOff (.mint 20) laterTranscript := by
  change (Bytes.toB256 (List.take 32 (encodeWords [(0 : B256)]))).toAdr = 0
  simp only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [List.take_of_length_le (show (0 : B256).toBytes.length ≤ 32 from
    Nat.le_of_eq (B256.length_toBytes 0)), B256.toB256_toBytes 0]
  rfl

/-- U3(ii), complete: on a history the mutant reaches (initialize, first mint, donation sync),
a fee-off later mint with positive supply succeeds under the round-up mutant with two LP
tokens where production issues one; the fee-off share-value inequality, which
`runTyped_feeOff_product` proves for the production run, fails for the mutant's committed state. -/
theorem mintRoundUp_breaks_feeOff_product :
    (runTypedWith mintRoundUp (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
      .done).status = .success [] ∧
    (runTypedWith mintRoundUp (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
      .done).frame.current.state = initialized ∧
    upMintRun.status = .success (encodeWords [1]) ∧
    upDonationRun.status = .success [] ∧ upDonationRun.frame.current.state = checkpoint ∧
    0 < checkpoint.totalSupply.toNat ∧ EntryFeeOff (.mint 20) laterTranscript ∧
    EntryNoShrink checkpoint context (.mint 20) laterTranscript ∧
    (runTyped checkpoint context (.mint 20) laterTranscript).status = .success (encodeWords [1]) ∧
    checkpoint.reserve0.val * checkpoint.reserve1.val *
        (runTyped checkpoint context (.mint 20) laterTranscript).frame.current.state.totalSupply.toNat ^ 2 ≤
      (runTyped checkpoint context (.mint 20) laterTranscript).frame.current.state.reserve0.val *
        (runTyped checkpoint context (.mint 20) laterTranscript).frame.current.state.reserve1.val *
        checkpoint.totalSupply.toNat ^ 2 ∧
    upLaterRun.status = .success (encodeWords [2]) ∧
    ¬ (checkpoint.reserve0.val * checkpoint.reserve1.val *
        upLaterRun.frame.current.state.totalSupply.toNat ^ 2 ≤
      upLaterRun.frame.current.state.reserve0.val * upLaterRun.frame.current.state.reserve1.val *
        checkpoint.totalSupply.toNat ^ 2) := by
  have positive : 0 < checkpoint.totalSupply.toNat := by
    rw [donation_execution.2]
    decide
  have production : (runTyped checkpoint context (.mint 20) laterTranscript).status =
      .success (encodeWords [1]) := by
    rw [donation_execution.2]
    decide +kernel
  refine ⟨?_, ?_, up_mint_execution.1, up_donation_execution.1, up_donation_execution.2, positive,
    later_feeOff, trivial, production,
    runTyped_feeOff_product positive later_feeOff trivial production, ?_, ?_⟩
  · rw [up_initialize]
    exact initialize_success
  · rw [up_initialize]
    rfl
  · rw [upLaterRun, donation_execution.2]
    rfl
  · rw [upLaterRun, donation_execution.2]
    decide +kernel

/-- A successful empty-returndata token transfer answer. -/
def transferOk : ExternalResult :=
  { success := true, returndata := [], codeExists := true, recoveryOutput := 0 }

/-- Swap out 1001 token1 for 1005013 token0 at the reached checkpoint (reserves 1002/1002). -/
def feeSwapTranscript : Transcript :=
  .next transferOk .done (.next (answer 1006015) .done (.next (answer 1) .done .done))

def feeMutantRun : RunResult :=
  runTypedWith (feeMutant 2) checkpoint context (.swap 0 1001 20 []) feeSwapTranscript

/-- U2 model mismatch, fee constant: at the reached checkpoint the production driver
rejects this swap with `UniswapV2: K`, while the 998 mutant (`feeMutant 2`) commits it
and stores reserves 1006015/1. -/
theorem feeMutant_disagrees :
    (runTyped checkpoint context (.swap 0 1001 20 []) feeSwapTranscript).status =
      .failed (.sourceGuard "UniswapV2: K") ∧
    feeMutantRun.status = .success [] ∧
    feeMutantRun.frame.current.state.reserve0.val = 1006015 ∧
    feeMutantRun.frame.current.state.reserve1.val = 1 := by
  rw [feeMutantRun, donation_execution.2]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The LP holder returns its token to the pair, as a burn caller does. -/
def burnReady : State :=
  (runTyped checkpoint { context with sender := 20 } (.transfer 17 1) .done).frame.current.state

/-- Initial balances, zero feeTo, both payout transfers accepted, final balances. -/
def burnTranscript : Transcript :=
  .next (answer 1002) .done (.next (answer 1002) .done (.next (answer 0) .done
    (.next transferOk .done (.next transferOk .done
      (.next (answer 1001) .done (.next (answer 1001) .done .done))))))

/-- U2 model mismatch, burn rounding: after an actual LP transfer to the pair, production
and the toward-the-user mutant both accept the same burn transcript, but production pays
and returns `(1, 1)` while the mutant pays and returns `(2, 2)`. -/
theorem burnRoundUp_disagrees :
    (runTyped checkpoint { context with sender := 20 } (.transfer 17 1) .done).status =
      .success (encodeWords [1]) ∧
    (runTyped burnReady context (.burn 20) burnTranscript).status =
      .success (encodeWords [1, 1]) ∧
    (runTypedWith burnRoundUp burnReady context (.burn 20) burnTranscript).status =
      .success (encodeWords [2, 2]) := by
  rw [burnReady, donation_execution.2]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end Mutants

end Blanc.Lift.UniswapV2Pair.ModelControls
