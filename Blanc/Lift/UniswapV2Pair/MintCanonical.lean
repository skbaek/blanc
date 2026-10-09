import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.UniswapV2Pair.StaticViewTurns
import Blanc.Lift.UniswapV2Pair.MutableTurns
import Blanc.Lift.PrecompileAnswer
import Blanc.Lift.UniswapV2Pair.PairTraceKeys
import Blanc.Lift.UniswapV2Pair.PairFeeSourceKeys

/-!
# Canonical mint frame

Every successful raw mint run at the Pair code consumes the typed source mint over its three
external observations (both token `balanceOf` replies and the factory `feeTo` reply), with
turn queues DERIVED from the actual child executions of the same pc-zero derivation. The
finite-storage freshness obligations of the protocol-fee recipient, the address-zero minimum
liquidity holder and the LP recipient are discharged from one trace-local (HASH-T) key
universe `WriterExtend K (mintTraceKeys root)`, a finite list of rows fixed by the root
execution (the fee recipient's row is drawn from the run's actual raw frames or a precompile's
answer to the fixed `feeTo()` request); no freshness premise is exported.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Every list of universe rows is fresh against every tracked subset of the universe. -/
private theorem mint_fresh_of_universe {U K : WriterKey → Prop} {ks : List WriterKey}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (touched : ∀ k ∈ ks, U k) : WriterFreshKeys K ks :=
  Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub touched

private theorem mint_single_row {U : WriterKey → Prop} {a : Adr}
    (row : U (.balance a)) : ∀ k ∈ lpMintTouched a, U k := by
  exact lpMintTouched_rows row

/-- The fee recipient's touched-row obligation holds in any separated universe holding its row. -/
theorem mint_feeFresh_of_universe {K U : WriterKey → Prop} {feeTo : B256}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (row : U (.balance feeTo.toAdr)) (st : State) (sevm : Sevm) (b : Devm) (r0 r1 : B256) :
    FeeMintFresh K st sevm b feeTo r0 r1 := by
  exact feeMintFresh_of_universe inj apart sub row st sevm b r0 r1

/-- The fee branch's tracked rows stay inside any universe holding the tracked rows and the
fee recipient's row. -/
theorem mint_feeKeys_sub {K U : WriterKey → Prop} {feeTo : B256}
    (sub : ∀ k, K k → U k) (row : U (.balance feeTo.toAdr))
    (st : State) (sevm : Sevm) (b : Devm) (r0 r1 : B256) :
    ∀ k, feeBranchSourceKeys K st sevm b feeTo r0 r1 k → U k := by
  exact pairFeeSourceKeys_sub sub row st sevm b r0 r1

/-- Both supply arms' LP-row obligations hold for every tracked subset of a separated universe
holding the address-zero and recipient rows. -/
theorem mint_afterFeeFresh_of_universe {K' U : WriterKey → Prop} {recipient : Adr}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K' k → U k)
    (zero : U (.balance (0 : B256).toAdr)) (row : U (.balance recipient)) (st : State) :
    MintAfterFeeFresh K' st recipient.toB256 := by
  have zeroRows : ∀ k ∈ lpMintTouched (0 : B256).toAdr, U k := mint_single_row zero
  have recipientRows : ∀ k ∈ lpMintTouched recipient.toB256.toAdr, U k := by
    rw [toAdr_toB256]
    exact mint_single_row row
  have subZero : ∀ k, WriterExtend K' (lpMintTouched (0 : B256).toAdr) k → U k := by
    intro k member
    rcases member with old | new
    · exact sub k old
    · exact zeroRows k new
  refine ⟨fun _ => ⟨mint_fresh_of_universe inj apart sub zeroRows,
    mint_fresh_of_universe inj apart subZero recipientRows⟩,
    fun _ => mint_fresh_of_universe inj apart sub recipientRows⟩

/-- A successful mint pricing segment keeps the frame's checkpoint and context and unlocks. -/
theorem mintAfterFee_finished_shape {frame : Frame} {observed : MintObserved} {fee : FeeResult}
    {finished : Frame} {bytes : Bytes}
    (result : frame.mintAfterFee observed fee = .finished finished bytes) :
    finished.checkpoint = frame.checkpoint ∧ finished.context = frame.context ∧
      finished.current.state.unlocked = 1 := by
  unfold Frame.mintAfterFee at result
  dsimp only at result
  split at result
  · simp only [Frame.fail, reduceCtorEq] at result
  · split at result
    · simp only [Frame.fail, reduceCtorEq] at result
    · split at result
      · split at result
        · simp only [Frame.fail, reduceCtorEq] at result
        · unfold Frame.finishUpdated at result
          split at result
          · simp only [Frame.fail, reduceCtorEq] at result
          · simp only [Frame.finishLocked, Frame.finish, Frame.withEvents, Frame.withUpdate,
              SegmentResult.finished.injEq] at result
            obtain ⟨frameEq, _⟩ := result
            subst frameEq
            exact ⟨rfl, rfl, rfl⟩
      · simp only [Frame.fail, reduceCtorEq] at result

/-- Raw image of the Pair's own events in a mint frame, as the bytecode encodes them: LP
`Transfer` and `Approval` (as `lockedOwnedRaw`), `Sync` and `Mint`. Burn and swap events have no
image here. -/
def mintOwnedRaw (pair : Adr) : Event → Option Log
  | .transfer source recipient value => some (transferRawLog pair source recipient value)
  | .approval owner spender value => some (approvalRawLog pair owner spender value)
  | .sync reserve0 reserve1 =>
      some ⟨pair, [updateSyncTopic], encodeWords [reserve0.toB256, reserve1.toB256]⟩
  | .mint sender amount0 amount1 =>
      some ⟨pair, [mintEventTopic, sender.toB256], amount0.toBytes ++ amount1.toBytes⟩
  | _ => none

private theorem mint_mintLP_events {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (minted : st.mintLP recipient value = .ok (post, events)) :
    events = [.transfer 0 recipient value] := by
  unfold State.mintLP at minted
  split at minted
  · split at minted
    · simp only [Except.ok.injEq, Prod.mk.injEq] at minted
      exact minted.2.symm
    · simp only [reduceCtorEq] at minted
  · simp only [reduceCtorEq] at minted

private theorem mint_update_event {st post : State} {ctx : Context} {b0 b1 : B256} {r0 r1 : Nat}
    {event : Event} {oracle : OracleUpdate}
    (updated : st.update ctx b0 b1 r0 r1 = .ok (post, event, oracle)) :
    event = .sync b0.toNat b1.toNat := by
  unfold State.update at updated
  split at updated
  · split at updated
    · simp only [Except.ok.injEq, Prod.mk.injEq] at updated
      exact updated.2.1.symm
    · simp only [reduceCtorEq] at updated
  · simp only [reduceCtorEq] at updated

/-- A finished mint pricing segment appends, at the frame's own origin, exactly the fee events,
the first-mint minimum, the recipient mint, `Sync` and `Mint`. -/
theorem mintAfterFee_finished_logs {frame : Frame} {observed : MintObserved} {fee : FeeResult}
    {finished : Frame} {bytes : Bytes}
    (result : frame.mintAfterFee observed fee = .finished finished bytes) :
    ∃ liquidity : Nat, bytes = encodeWords [liquidity.toB256] ∧
      finished.current.logs = frame.current.logs ++
        (fee.events ++ (if fee.state.totalSupply = 0 then [Event.transfer 0 0 1000] else []) ++
          [Event.transfer 0 observed.recipient liquidity.toB256,
            Event.sync observed.balance0.toNat observed.balance1.toNat,
            Event.mint frame.context.sender observed.amount0 observed.amount1]).map
          (PendingLog.owned frame.origin) := by
  unfold Frame.mintAfterFee at result
  dsimp only at result
  split at result
  · simp only [Frame.fail, reduceCtorEq] at result
  · rename_i liquidity _
    split at result
    · simp only [Frame.fail, reduceCtorEq] at result
    · rename_i postMinimum minimumEvents initial
      split at result
      · split at result
        · simp only [Frame.fail, reduceCtorEq] at result
        · rename_i post events minted
          unfold Frame.finishUpdated at result
          split at result
          · simp only [Frame.fail, reduceCtorEq] at result
          · rename_i updatedPost event oracle updated
            simp only [Frame.finishLocked, Frame.finish, Frame.withEvents, Frame.withUpdate,
              SegmentResult.finished.injEq] at result
            obtain ⟨frameEq, bytesEq⟩ := result
            subst frameEq
            have minimum : minimumEvents =
                if fee.state.totalSupply = 0 then [.transfer 0 0 1000] else [] := by
              by_cases zero : fee.state.totalSupply = 0
              · rw [ite_eq_left zero] at initial ⊢
                exact mint_mintLP_events initial
              · rw [ite_eq_right zero] at initial ⊢
                simp only [Except.ok.injEq, Prod.mk.injEq] at initial
                exact initial.2.symm
            refine ⟨liquidity, bytesEq.symm, ?_⟩
            rw [mint_mintLP_events minted, mint_update_event updated, minimum]
            simp only [Frame.origin, List.map_append, List.map_cons, List.map_nil,
              List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
      · simp only [Frame.fail, reduceCtorEq] at result

/-- The typed mint events map, under `mintOwnedRaw`, onto the exact raw mint log list. -/
theorem mint_logs_raw {pair recipient sender feeTo : Adr} {origin : ReceiptOrigin}
    {fee : FeeResult} {feeLogs : List Log} {liquidity b0 b1 a0 a1 : B256}
    (feeShape : (fee.events = [] ∧ feeLogs = []) ∨ ∃ L : B256, L ≠ 0 ∧
      fee.events = [.transfer 0 feeTo L] ∧ feeLogs = [lpMintRawLog pair feeTo L]) :
    ((fee.events ++ (if fee.state.totalSupply = 0 then [Event.transfer 0 0 1000] else []) ++
        [Event.transfer 0 recipient liquidity, Event.sync b0.toNat b1.toNat,
          Event.mint sender a0 a1]).map
        (PendingLog.owned origin)).map (PendingLog.rawWith (mintOwnedRaw pair)) =
      (feeLogs ++ (if fee.state.totalSupply = 0 then
          [lpMintRawLog pair (0 : B256).toAdr 1000] else []) ++
        [lpMintRawLog pair recipient liquidity, ⟨pair, [updateSyncTopic], encodeWords [b0, b1]⟩,
          ⟨pair, [mintEventTopic, sender.toB256], a0.toBytes ++ a1.toBytes⟩]).map some := by
  have zeroAdr : (0 : B256).toAdr = (0 : Adr) := rfl
  have zeroWord : (0 : Adr).toB256 = (0 : B256) := rfl
  have feePart : (fee.events.map (PendingLog.owned origin)).map
      (PendingLog.rawWith (mintOwnedRaw pair)) = feeLogs.map some := by
    rcases feeShape with ⟨events, logs⟩ | ⟨L, _, events, logs⟩
    · rw [events, logs]
      rfl
    · rw [events, logs]
      simp only [List.map_cons, List.map_nil, PendingLog.rawWith, mintOwnedRaw, transferRawLog,
        lpMintRawLog, zeroWord]
  have minimumPart : (((if fee.state.totalSupply = 0 then [Event.transfer 0 0 1000] else []).map
      (PendingLog.owned origin)).map (PendingLog.rawWith (mintOwnedRaw pair))) =
      (if fee.state.totalSupply = 0 then [lpMintRawLog pair (0 : B256).toAdr 1000] else []).map
        some := by
    split
    · simp only [List.map_cons, List.map_nil, PendingLog.rawWith, mintOwnedRaw, transferRawLog,
        lpMintRawLog, zeroAdr, zeroWord]
    · rfl
  simp only [List.map_append, feePart, minimumPart, List.map_cons, List.map_nil,
    PendingLog.rawWith, mintOwnedRaw, transferRawLog, lpMintRawLog, zeroWord, toB256_toNat]

/-- The three actual STATICCALL steps of a mint run, at the typed targets, with their reply
buffers and the actual extcodesize bits the bytecode checks before each call (token0, token1,
factory), each bit read from the world of the same step. -/
def MintObservedSteps (D : Exec.Deriv) (current : Checkpoint) (sevm : Sevm)
    (out0 out1 outF : Bytes) : Prop :=
  ∃ (g0 g1 gF : B256) (S0 S1 SF : List B256) (M0 M1 MF : Mem) (c0 c1 cF : Nat)
    (w0 w1 wF d0 d1 dF : Devm),
    Blanc.Lift.StepIn D sevm (St w0 (g0 :: current.state.token0.toB256 :: S0) M0 c0)
      (.exec .staticcall) d0 ∧ d0.returnData = out0 ∧ (w0.getCode current.state.token0).size ≠ 0 ∧
    Blanc.Lift.StepIn D sevm (St w1 (g1 :: current.state.token1.toB256 :: S1) M1 c1)
      (.exec .staticcall) d1 ∧ d1.returnData = out1 ∧ (w1.getCode current.state.token1).size ≠ 0 ∧
    Blanc.Lift.StepIn D sevm (St wF (gF :: current.state.factory.toB256 :: SF) MF cF)
      (.exec .staticcall) dF ∧ dF.returnData = outF ∧ (wF.getCode current.state.factory).size ≠ 0

/-- Per-call static-view provenance: an empty queue at an enabled precompile, or exactly the
retained static Pair turns of the actually committed child. -/
def MintViewProvenance (root : Exec.Deriv) (pair target : Adr) (views : List StaticViewTurn) :
    Prop :=
  ViewQueueOrigin root root.sevm pair target views

end Blanc.Lift.UniswapV2Pair
