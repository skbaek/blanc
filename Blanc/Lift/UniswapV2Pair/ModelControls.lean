import Blanc.Lift.UniswapV2Pair.Properties

/-! Required kernel statement controls on actual reachable typed-model states.
The upward control changes the bounded pricing result and composes unchanged
LP issuance and reserve update; it is not a mutated whole-driver refinement.
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

def pricingFrame : Frame :=
  { context := context, entry := .mint 20,
    checkpoint := { state := checkpoint, logs := [], updates := [] },
    current := { state := { checkpoint with unlocked := 0 }, logs := [], updates := [] },
    segment := 3, afterCall := some .mintFeeTo }

def laterObserved : MintObserved := mintObservation 20 checkpoint.cachedReserves 1004 1004

def laterFee : FeeResult :=
  { state := pricingFrame.current.state, feeOn := false, minted := 0, events := [] }

/-- The bounded pricing seam is exactly the actual later-mint three-query source prefix. -/
theorem later_prefix :
    runTyped checkpoint context (.mint 20) laterTranscript =
      drive 2 (pricingFrame.mintAfterFee laterObserved laterFee) .done := by
  rw [laterObserved, laterFee, pricingFrame, donation_execution.2]
  rfl

/-- The unchanged source price at this reached checkpoint is one LP token. -/
theorem later_price :
    mintAmount laterObserved.amount0 laterObserved.amount1 laterFee.state.totalSupply
      laterObserved.reserves.reserve0.val laterObserved.reserves.reserve1.val = .ok 1 := by
  rw [laterObserved, laterFee, pricingFrame, donation_execution.2]
  rfl

def upwardPost : State :=
  { laterFee.state with
    totalSupply := laterFee.state.totalSupply + 2,
    balanceOf := Blanc.ledgerCredit laterFee.state.balanceOf 20 2 }

def upwardUpdated : State :=
  { upwardPost with reserve0 := ⟨1004, by decide⟩, reserve1 := ⟨1004, by decide⟩ }

def upwardUpdate : OracleUpdate :=
  { oldReserve0 := 1002, oldReserve1 := 1002, oldTimestamp := 0,
    timestamp := 0, elapsed := 0, increment0 := 0, increment1 := 0 }

/-- The upward price is still admitted by the original checked LP issuance transition. -/
theorem upward_issuance :
    laterFee.state.mintLP 20 2 = .ok (upwardPost, [.transfer 0 20 2]) := by
  rw [upwardPost, laterFee, pricingFrame, donation_execution.2]
  rfl

/-- The same original reserve update stores the deposited balances after upward issuance. -/
theorem upward_update :
    upwardPost.update context 1004 1004 laterObserved.reserves.reserve0.val
      laterObserved.reserves.reserve1.val =
      .ok (upwardUpdated, .sync 1004 1004, upwardUpdate) := by
  rw [upwardUpdated, upwardPost, laterFee, laterObserved, pricingFrame, donation_execution.2]
  dsimp only [checkpointExpected, mintExpected, State.empty, context, State.cachedReserves,
    mintObservation, upwardUpdate]
  rw [State.update]
  have balanceBound : (1004 : B256).toNat < 2 ^ 112 := by decide
  rw [dite_eq_left balanceBound, dite_eq_left balanceBound]
  dsimp only []
  have zeroTimestamp : (0 : UInt32).toNat = 0 := rfl
  simp only [B256.toNat_zero, zeroTimestamp, Nat.zero_mod, Nat.zero_add, Nat.sub_zero,
    Nat.mod_self, Nat.lt_irrefl, false_and, ite_false]
  rfl

/-- Required upward-rounding pricing-seam counterexample, not a mutated-driver refinement. -/
theorem upward_pricing_seam_required :
    (runTyped (State.empty 16 0) { context with sender := 16 } (.initialize 18 19)
      .done).status = .success [] ∧
    mintRun.status = .success (encodeWords [1]) ∧ donationRun.status = .success [] ∧
    runTyped checkpoint context (.mint 20) laterTranscript =
      drive 2 (pricingFrame.mintAfterFee laterObserved laterFee) .done ∧
    mintAmount laterObserved.amount0 laterObserved.amount1 laterFee.state.totalSupply
      laterObserved.reserves.reserve0.val laterObserved.reserves.reserve1.val = .ok 1 ∧
    min ((2 * 1001 + 1002 - 1) / 1002) ((2 * 1001 + 1002 - 1) / 1002) = 2 ∧
    laterFee.state.mintLP 20 2 = .ok (upwardPost, [.transfer 0 20 2]) ∧
    upwardPost.update context 1004 1004 laterObserved.reserves.reserve0.val
      laterObserved.reserves.reserve1.val =
      .ok (upwardUpdated, .sync 1004 1004, upwardUpdate) ∧
    ¬ (checkpoint.reserve0.val * checkpoint.reserve1.val * upwardUpdated.totalSupply.toNat ^ 2 ≤
      upwardUpdated.reserve0.val * upwardUpdated.reserve1.val * checkpoint.totalSupply.toNat ^ 2) := by
  refine ⟨initialize_success, mint_execution.1, donation_execution.1, later_prefix,
    later_price, ?_, upward_issuance, upward_update, ?_⟩
  · decide
  · rw [upwardUpdated, upwardPost, laterFee, pricingFrame, donation_execution.2]
    decide

end Blanc.Lift.UniswapV2Pair.ModelControls
