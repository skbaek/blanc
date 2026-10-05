import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.UniswapV2Pair.StaticViewTurns
import Blanc.Lift.UniswapV2Pair.MutableTurns
import Blanc.Lift.PrecompileAnswer

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

/-- The LP row of a reply's first word (the fee recipient's row when the reply answers
`feeTo()`). -/
def mintReplyRow (out : Bytes) : WriterKey := .balance (Bytes.toB256 (out.take 32)).toAdr

/-- Every possible `feeTo()` reply row of a mint run, as a finite list fixed by the root alone:
the reply row of every successful actually entered raw frame of the run, and the answer row of
every precompile to the fixed 4-byte `feeTo()` request under the root's `MODEXP` pricing. -/
noncomputable def mintFeeReplyKeys (root : Exec.Deriv) : List WriterKey :=
  (Exec.rawFrameRoots root.exc).filterMap (fun F =>
    match F.exn with
    | .ok d => some (mintReplyRow d.output)
    | .error _ => none) ++
  precompileRunAddresses.filterMap (fun adr =>
    (precompileAnswer (ExternalOperation.encode .feeTo) root.sevm.benvStat.rules.modexp
      adr).map mintReplyRow)

/-- Trace rows of a mint run fixed by the root alone: the decoded rows of every actually entered
Pair frame, the two LP rows the entry may write (address zero, the decoded recipient) and every
possible fee-recipient row (`mintFeeReplyKeys`). -/
noncomputable def mintTraceKeys (root : Exec.Deriv) : List WriterKey :=
  ((Exec.rawFrameRoots root.exc).flatMap fun F =>
    if F.sevm.currentTarget = root.sevm.currentTarget then staticViewDecodedKeys F.sevm else []) ++
  (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord root.sevm 4).toAdr) ++
  mintFeeReplyKeys root

theorem mintTraceKeys_frame {root : Exec.Deriv} {F : Exec.Deriv}
    (member : F ∈ Exec.rawFrameRoots root.exc)
    (target : F.sevm.currentTarget = root.sevm.currentTarget) :
    ∀ k ∈ staticViewDecodedKeys F.sevm, k ∈ mintTraceKeys root := by
  intro k touched
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨F, member, ?_⟩))
  rw [ite_eq_left target]
  exact touched

theorem mintTraceKeys_rows (root : Exec.Deriv) :
    .balance (0 : B256).toAdr ∈ mintTraceKeys root ∧
    .balance (Sevm.dataWord root.sevm 4).toAdr ∈ mintTraceKeys root := by
  refine ⟨?_, ?_⟩ <;>
    simp only [mintTraceKeys, lpMintTouched, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, true_or, or_true]

/-- Every list of universe rows is fresh against every tracked subset of the universe. -/
private theorem mint_fresh_of_universe {U K : WriterKey → Prop} {ks : List WriterKey}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (touched : ∀ k ∈ ks, U k) : WriterFreshKeys K ks :=
  Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub touched

private theorem mint_single_row {U : WriterKey → Prop} {a : Adr}
    (row : U (.balance a)) : ∀ k ∈ lpMintTouched a, U k := by
  intro k member
  simp only [lpMintTouched, List.mem_cons, List.not_mem_nil, or_false] at member
  rw [member]
  exact row

/-- The fee recipient's touched-row obligation holds in any separated universe holding its row. -/
theorem mint_feeFresh_of_universe {K U : WriterKey → Prop} {feeTo : B256}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (row : U (.balance feeTo.toAdr)) (st : State) (sevm : Sevm) (b : Devm) (r0 r1 : B256) :
    FeeMintFresh K st sevm b feeTo r0 r1 := by
  intro _ _ _ _
  exact mint_fresh_of_universe inj apart sub (mint_single_row row)

/-- The fee branch's tracked rows stay inside any universe holding the tracked rows and the
fee recipient's row. -/
theorem mint_feeKeys_sub {K U : WriterKey → Prop} {feeTo : B256}
    (sub : ∀ k, K k → U k) (row : U (.balance feeTo.toAdr))
    (st : State) (sevm : Sevm) (b : Devm) (r0 r1 : B256) :
    ∀ k, feeBranchSourceKeys K st sevm b feeTo r0 r1 k → U k := by
  intro k tracked
  have extended : WriterExtend K (lpMintTouched feeTo.toAdr) k → U k := by
    intro member
    rcases member with old | new
    · exact sub k old
    · exact mint_single_row row k new
  unfold feeBranchSourceKeys at tracked
  split at tracked
  · exact sub k tracked
  · split at tracked
    · exact sub k tracked
    · split at tracked
      · split at tracked
        · exact sub k tracked
        · exact extended tracked
      · exact sub k tracked

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

/-- The three observed replies, each preceded by a turn queue that leaves its frame unchanged,
consume the typed source mint exactly up to its finished pricing segment. -/
theorem mint_source_exact_consumption {current : Checkpoint} {ctx : Context} {recipient : Adr}
    {out0 out1 outF : Bytes} {T0 T1 TF : Transcript} {e0 e1 eF : TurnsResult}
    {finished : Frame} {bytes : Bytes}
    (handlers : MintBalanceHandlerResult current ctx recipient out0 out1)
    (fee : resumeSegment (mintSourceFeeFrame current ctx recipient)
      (requestFor .mintFeeTo current.state.factory .feeTo)
      (.mintFee (mintBalanceObserved current.state recipient (Bytes.toB256 (out0.take 32))
        (Bytes.toB256 (out1.take 32))))
      (feeObservedResult outF) = .finished finished bytes)
    (turns0 : ExactTurns (mintSourceLockedFrame current ctx recipient)
      (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)) 0 T0 e0)
    (frame0 : e0.frame = mintSourceLockedFrame current ctx recipient)
    (turns1 : ExactTurns ((mintSourceLockedFrame current ctx recipient).beginResume
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)))
      (requestFor .mintBalance1 current.state.token1 (.balanceOf ctx.pair)) 0 T1 e1)
    (frame1 : e1.frame = (mintSourceLockedFrame current ctx recipient).beginResume
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)))
    (turnsF : ExactTurns (mintSourceFeeFrame current ctx recipient)
      (requestFor .mintFeeTo current.state.factory .feeTo) 0 TF eF)
    (frameF : eF.frame = mintSourceFeeFrame current ctx recipient) :
    ExactConsumes (startTyped current ctx (.mint recipient))
      (.next (feeObservedResult out0) T0 (.next (feeObservedResult out1) T1
        (.next (feeObservedResult outF) TF .done)))
      { status := .success bytes, frame := finished, remaining := .done,
        childReturns := e0.childReturns ++ (e1.childReturns ++ (eF.childReturns ++ [])) } := by
  obtain ⟨start, resume0, resume1⟩ := handlers
  rw [start]
  have last : ExactConsumes (.suspended (mintSourceFeeFrame current ctx recipient)
      (requestFor .mintFeeTo current.state.factory .feeTo)
      (.mintFee (mintBalanceObserved current.state recipient (Bytes.toB256 (out0.take 32))
        (Bytes.toB256 (out1.take 32)))))
      (.next (feeObservedResult outF) TF .done)
      { status := .success bytes, frame := finished, remaining := .done,
        childReturns := eF.childReturns ++ [] } := by
    refine ExactConsumes.nextCall (result := feeObservedResult outF)
      (out := ⟨.success bytes, finished, .done, []⟩) rfl
      (fun absent => by cases absent) turnsF ?_
    simp only [feeObservedResult, ite_true, frameF]
    change ExactConsumes (resumeSegment _ _ _ (feeObservedResult outF)) _ _
    rw [fee]
    exact ExactConsumes.finished finished bytes
  have middle : ExactConsumes (resumeSegment (mintSourceLockedFrame current ctx recipient)
      (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair))
      (.mintBalance0 recipient current.state.cachedReserves) (feeObservedResult out0))
      (.next (feeObservedResult out1) T1 (.next (feeObservedResult outF) TF .done))
      { status := .success bytes, frame := finished, remaining := .done,
        childReturns := e1.childReturns ++ (eF.childReturns ++ []) } := by
    rw [resume0]
    refine ExactConsumes.nextCall (result := feeObservedResult out1)
      (out := ⟨.success bytes, finished, .done, eF.childReturns ++ []⟩) rfl
      (fun absent => by cases absent) turns1 ?_
    simp only [feeObservedResult, ite_true, frame1]
    rw [show (feeObservedResult out1 : ExternalResult) =
      { success := true, returndata := out1, codeExists := true, recoveryOutput := 0 } from rfl]
      at resume1
    rw [resume1]
    exact last
  refine ExactConsumes.nextCall (result := feeObservedResult out0)
      (out := ⟨.success bytes, finished, .done, e1.childReturns ++ (eF.childReturns ++ [])⟩) rfl
      (fun absent => by cases absent) turns0 ?_
  simp only [feeObservedResult, ite_true, frame0]
  exact middle

private theorem mint_St_getStor (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    Devm.getStor (St x S M g) a = Devm.getStor x a := rfl

private theorem mint_St_getCode (x : Devm) (S : List B256) (M : Mem) (g : Nat) (a : Adr) :
    (St x S M g).getCode a = x.getCode a := rfl

private theorem mint_operands (x : Devm) (S : List B256) (M : Mem) (g : Nat) :
    S <<+ (St x S M g).stack := by
  simpa only [List.append_nil, St.stack] using pref_append S ([] : List B256)

private theorem mint_tAAB_getStor (base : Devm) (a x : Adr) :
    Devm.getStor (temporalAccountAccessBase base a) x = Devm.getStor base x := by
  unfold temporalAccountAccessBase
  split <;> rfl

private theorem mint_tAAB_getCode (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  unfold temporalAccountAccessBase
  split <;> rfl

/-- The actual `feeTo()` STATICCALL of the root frame returns a reply whose row is in
`mintFeeReplyKeys root`: a framed callee's child is a raw frame root of the run, and a frameless
successful callee is a precompile answering the fixed request. -/
theorem mint_feeReply_mem {root : Exec.Deriv} {w d : Devm} {g t oi os : B256} {S : List B256}
    {M : Mem} {c : Nat} (fork : CoveredFork root.sevm.benvStat.fork) (wf : Mem.Wf M)
    (call : Blanc.Lift.StepIn root root.sevm
      (St w (g :: t :: 128 :: 4 :: oi :: os :: S) (feeRequestMemory M) c) (.exec .staticcall) d)
    (flag : ∃ f rest, d.stack = f :: rest ∧ f ≠ 0) :
    mintReplyRow d.returnData ∈ mintTraceKeys root := by
  refine List.mem_append_right _ ?_
  obtain ⟨xl, inRoots, pc, stepRun⟩ := call
  have filled : Xlot.Filled xl := by
    cases xl with
    | none => trivial
    | some p =>
      obtain ⟨evm, exn⟩ := p
      obtain ⟨e, _⟩ := inRoots
      exact ⟨e⟩
  rcases of_step_staticcall_val_with_depth_frame_cause (g := g) (t := t) (ii := 128) (is := 4)
      (oi := oi) (os := os) (xs := S) (mint_operands _ _ _ _) filled stepRun fork with
      ⟨failed, _⟩ | ⟨parent, child, dp, na, code, avail, _, _, _, _, _, _, _, _,
        process, clean, _, _, returned, _, _, _⟩
  · obtain ⟨f, rest, flagStack, nonzero⟩ := flag
    rw [flagStack] at failed
    exact (nonzero (pref_head_unique failed (pref_append [f] rest)).symm).elim
  · rw [returned]
    rcases Blanc.Lift.ProcessMessage.ok_output process clean with
      ⟨_, adr, listed, answer⟩ | ⟨evm, raw, slot, rawEq⟩
    · refine List.mem_append_right _ (List.mem_filterMap.mpr ⟨adr, listed, ?_⟩)
      have request :
          ((St w (g :: t :: 128 :: 4 :: oi :: os :: S) (feeRequestMemory M) c).memory.read
          (128 : B256).toNat (4 : B256).toNat).1 = ExternalOperation.encode .feeTo :=
        feeRequestMemory_read wf
      change precompileAnswer ((St w (g :: t :: 128 :: 4 :: oi :: os :: S) (feeRequestMemory M)
        c).memory.read (128 : B256).toNat (4 : B256).toNat).1 root.sevm.benvStat.rules.modexp adr =
        some child.output at answer
      rw [request] at answer
      rw [answer]
      rfl
    · subst slot
      subst rawEq
      obtain ⟨childRun, roots⟩ := inRoots
      refine List.mem_append_left _ (List.mem_filterMap.mpr
        ⟨⟨evm.pc, evm.sta, evm.dyna, .ok child, childRun⟩, roots _ List.mem_cons_self, rfl⟩)

private theorem mint_feeMemory_wf (sevm : Sevm) (out0 out1 : Bytes) :
    Mem.Wf (balanceReplyMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
      sevm.currentTarget out1) :=
  (balanceReplyMemory_ptr out1 (balanceRequestMemory_ptr
    (balanceReplyMemory_ptr out0 (balanceRequestMemory_ptr getterInitMemory_ptr _)) _)).wf

private theorem mint_size_ne {c : ByteArray} (bit : c.size.toB256 ≠ 0) : c.size ≠ 0 := by
  intro empty
  rw [empty] at bit
  exact bit rfl

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
  views = [] ∧ root.sevm.benvStat.rules.isPrecomp target ∨
    ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw),
      Execution.commits raw = true ∧
      (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots root.exc) ∧
      views.map Prod.fst = (Exec.retainedTargetTurnsAt pair [] childRun).filterMap Sum.getRight?

private theorem mint_encodeWord_inj {x y : B256} (same : encodeWords [x] = encodeWords [y]) :
    x = y := by
  have words := congrArg Bytes.toB256 same
  simpa only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    B256.toB256_toBytes] using words

/-- What the canonical mint frame derives from one successful raw mint run `run` (see
`mint_bytecode_exact_consumes`): the actual observation steps, the exact typed consumption, the
final frame shape, the storage transport, the fee result and its log, the exact raw log list and
its typed pending logs, the return word, view authenticity and per-call provenance. -/
def MintCanonicalResult (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat)
    {sevm : Sevm} {b post : Devm} {G : Nat} (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Prop :=
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let ctx := writerContext sevm invocation
    let recipient := (Sevm.dataWord sevm 4).toAdr
    sevm.value = 0 ∧ sevm.isStatic = false ∧
    ∃ (out0 out1 outF : Bytes), MintObservedSteps root current sevm out0 out1 outF ∧
      let balance0 := Bytes.toB256 (out0.take 32)
      let balance1 := Bytes.toB256 (out1.take 32)
      let feeTo := (Bytes.toB256 (outF.take 32)).toAdr
      ∃ (views0 views1 viewsF : List StaticViewTurn) (final : Frame) (rets : List ChildReturn)
        (K' : WriterKey → Prop) (liquidity : Nat) (fee : FeeResult) (feeLogs : List Log)
        (added : List PendingLog),
        ExactConsumes (startTyped current ctx (.mint recipient))
          (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
            (.next (feeObservedResult out1) (staticViewTranscript views1 .done)
              (.next (feeObservedResult outF) (staticViewTranscript viewsF .done) .done)))
          { status := .success (encodeWords [liquidity.toB256]), frame := final,
            remaining := .done, childReturns := rets } ∧
        final.checkpoint = current ∧ final.context = ctx ∧
        final.current.state.unlocked = 1 ∧
        (∀ k, K' k → WriterExtend K (mintTraceKeys root) k) ∧
        WriterRep K' (post.getStor sevm.currentTarget) final.current.state ∧
        mintFee { current.state with unlocked := 0 } feeTo current.state.reserve0.val
          current.state.reserve1.val = .ok fee ∧
        ((fee.events = [] ∧ feeLogs = []) ∨ ∃ L : B256, L ≠ 0 ∧
          fee.events = [.transfer 0 feeTo L] ∧
          feeLogs = [lpMintRawLog sevm.currentTarget feeTo L]) ∧
        post.logs = b.logs ++ feeLogs ++
          (if fee.state.totalSupply = 0 then
            [lpMintRawLog sevm.currentTarget (0 : B256).toAdr 1000] else []) ++
          [lpMintRawLog sevm.currentTarget recipient liquidity.toB256,
            ⟨sevm.currentTarget, [updateSyncTopic], encodeWords [balance0, balance1]⟩,
            ⟨sevm.currentTarget, [mintEventTopic, sevm.caller.toB256],
              (balance0 - current.state.reserve0.val.toB256).toBytes ++
                (balance1 - current.state.reserve1.val.toB256).toBytes⟩] ∧
        final.current.logs = current.logs ++ added ∧
        (∃ L : List Log, post.logs = b.logs ++ L ∧
          added.map (PendingLog.rawWith (mintOwnedRaw sevm.currentTarget)) = L.map some) ∧
        post.output = encodeWords [liquidity.toB256] ∧
        (∀ picked ∈ views0 ++ views1 ++ viewsF,
          Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
          picked.1.frame.sevm.currentTarget = sevm.currentTarget ∧
          picked.1.frame.sevm.isStatic = true) ∧
        MintViewProvenance root sevm.currentTarget current.state.token0 views0 ∧
        MintViewProvenance root sevm.currentTarget current.state.token1 views1 ∧
        MintViewProvenance root sevm.currentTarget current.state.factory viewsF

/-- **Canonical mint frame.** Every successful raw mint run at the Pair code consumes the typed
source mint over its three actual observations (token0 and token1 `balanceOf`, factory `feeTo`)
with static-view turn queues derived from the actual children of the same derivation. Under
trace-local HASH-T over the run's key universe `WriterExtend K (mintTraceKeys root)` (the
tracked rows plus a finite list of rows fixed by the root execution alone), it yields the exact Pair storage, the exact raw log
list (fee mint, first-mint minimum to address zero, recipient mint, Sync, Mint) together with
the typed pending logs that map onto it, the return word, the final unlock and the original
checkpoint. -/
theorem mint_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (inj : WriterInj
      (WriterExtend K (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (apart : WriterApart
      (WriterExtend K (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    MintCanonicalResult K current invocation run := by
  unfold MintCanonicalResult
  intro root ctx recipient
  have source := (mintBytecode_public_source_inv (K := K) (current := current) codeEq fork rep
    invocation selector run).1
  unfold MintPublicSourceResult at source
  dsimp only at source
  obtain ⟨value, _, _, calleeGas, calleePost, callee, mem, unlockedRaw, nonstatic,
    gw0, callGas0, d0, out0, decodedGas0, gw1, callGas1, d1, out1, decodedGas1, feeGas, feePost,
    code0, call0, post0, long0, width0, answered0, decoded0, code1, call1, post1, long1, width1,
    answered1, stor0, stor1, logs1, output1, decoded1, cover0, cover1, feeRun, suffix,
    bound0, bound1, typedFinished, handlers, cache0, cache1, token0Target, token1Target,
    factoryTarget⟩ := source
  unfold MintPublicTypedFeeFinished at typedFinished
  obtain ⟨gwF, callGasF, dF, outF, callF, postF, widthF, boundF, answerF, feeImplication⟩ :=
    typedFinished
  -- the trace universe: tracked rows, root rows and the actual fee recipient's row
  have sub : ∀ k, K k → WriterExtend K (mintTraceKeys root) k := fun _ tracked => Or.inl tracked
  have rows : WriterExtend K (mintTraceKeys root) (.balance (0 : B256).toAdr) ∧
      WriterExtend K (mintTraceKeys root) (.balance (Sevm.dataWord sevm 4).toAdr) :=
    ⟨Or.inr (mintTraceKeys_rows root).1, Or.inr (mintTraceKeys_rows root).2⟩
  have feeRow :
      WriterExtend K (mintTraceKeys root) (.balance (Bytes.toB256 (outF.take 32)).toAdr) := by
    refine Or.inr ?_
    have member := mint_feeReply_mem fork (mint_feeMemory_wf sevm out0 out1) callF
      ⟨1, _, postF.stack, by decide⟩
    rw [postF.returnData] at member
    exact member
  -- raw worlds and code
  have nonemptyList : (b.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have lockedRep := rep.mint_locked_world (sevm := sevm) (b := b)
  have lockedCode : ∀ a, (mintLockedWorld sevm b).getCode a = b.getCode a := by
    intro a
    rw [mintLockedWorld, afterSstore_getCode, afterSload_getCode]
  have codeD0 : d0.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [Blanc.Lift.StepIn.codePreserve call0 sevm.currentTarget
      (by rw [mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, afterSload_getCode,
        lockedCode]; exact nonemptyList),
      mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, afterSload_getCode, lockedCode]
  have codeD1 : d1.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
    rw [Blanc.Lift.StepIn.codePreserve call1 sevm.currentTarget
      (by rw [mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, codeD0]; exact nonemptyList),
      mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, codeD0]
  have natCache0 : (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat =
      current.state.reserve0.val := by
    rw [cache0, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have natCache1 : (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat =
      current.state.reserve1.val := by
    rw [cache1, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
  have word0 : ((afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr.toB256 =
      current.state.token0.toB256 := by
    rw [← token0Target, toAdr_toB256]
  have word1 : (d0.getStorVal sevm.currentTarget 7).toAdr.toB256 = current.state.token1.toB256 := by
    rw [← token1Target, toAdr_toB256]
  have wordF : feeFactoryWord sevm d1 = current.state.factory.toB256 := by
    rw [← factoryTarget]
    unfold feeFactoryWord
    rw [toAdr_toB256]
  have call0' := call0
  rw [word0] at call0'
  have call1' := call1
  rw [word1] at call1'
  have callF' := callF
  rw [wordF] at callF'
  -- the three static-view turn queues
  let ctxM := writerContext sevm invocation
  have good : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, WriterExtend K (mintTraceKeys root) k :=
    fun F member target k touched => Or.inr (mintTraceKeys_frame member target k touched)
  obtain ⟨views0, turns0, auth0, prov0⟩ :=
    pair_static_call_turns (frame := mintSourceLockedFrame current ctxM recipient)
      (request := requestFor .mintBalance0 current.state.token0 (.balanceOf ctxM.pair))
      inj apart sub sem image call0 (mint_operands _ _ _ _)
      (by rw [mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, afterSload_getCode,
        lockedCode]; exact installed)
      (by rw [mint_St_getStor, mint_tAAB_getStor, afterSload_getStor, afterSload_getStor]
          exact lockedRep)
      rfl fork ⟨1, _, post0.stack, by decide⟩ good
  obtain ⟨views1, turns1, auth1, prov1⟩ :=
    pair_static_call_turns (frame := (mintSourceLockedFrame current ctxM recipient).beginResume
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctxM.pair)))
      (request := requestFor .mintBalance1 current.state.token1 (.balanceOf ctxM.pair))
      inj apart sub sem image call1 (mint_operands _ _ _ _)
      (by change some (Devm.getCode _ sevm.currentTarget).toList = _
          rw [mint_St_getCode, mint_tAAB_getCode, afterSload_getCode, codeD0]; exact installed)
      (by rw [mint_St_getStor, mint_tAAB_getStor, afterSload_getStor, stor0]
          exact lockedRep)
      rfl fork ⟨1, _, post1.stack, by decide⟩ good
  obtain ⟨viewsF, turnsF, authF, provF⟩ :=
    pair_static_call_turns (frame := mintSourceFeeFrame current ctxM recipient)
      (request := requestFor .mintFeeTo current.state.factory .feeTo)
      inj apart sub sem image callF (mint_operands _ _ _ _)
      (by change some (Devm.getCode _ sevm.currentTarget).toList = _
          rw [mint_St_getCode, feeFactoryCallWorld, mint_tAAB_getCode, feeFactoryLoadWorld,
            afterSload_getCode, codeD1]; exact installed)
      (by rw [mint_St_getStor, feeFactoryCallWorld, mint_tAAB_getStor, feeFactoryLoadWorld,
        afterSload_getStor, stor1]
          exact lockedRep)
      rfl fork ⟨1, _, postF.stack, by decide⟩ good
  -- discharge both freshness obligations in the trace universe
  obtain ⟨observation, dEq, outEq, rest⟩ :=
    feeImplication (mint_feeFresh_of_universe inj apart sub feeRow _ _ _ _ _)
  obtain ⟨frameResult, liquidity, finished, feeEq⟩ :=
    rest (mint_afterFeeFresh_of_universe inj apart (mint_feeKeys_sub sub feeRow _ _ _ _ _)
      rows.1 rows.2 _)
  have consumed := mint_source_exact_consumption handlers feeEq turns0 rfl turns1 rfl turnsF rfl
  obtain ⟨liq', keys, fin', d, keysEq, typedEq, wrep, halted, output, logs⟩ := frameResult
  have resume := observation.resume_mint (mintSourceFeeFrame current ctxM recipient)
    (mintBalanceObserved current.state recipient (Bytes.toB256 (out0.take 32))
      (Bytes.toB256 (out1.take 32))) rfl natCache0.symm natCache1.symm
  rw [factoryTarget, dEq, outEq] at resume
  obtain ⟨liqTyped, bytesTyped, logsTyped⟩ :=
    mintAfterFee_finished_logs (resume.2.symm.trans feeEq)
  have same := feeEq.symm.trans (resume.2.trans typedEq)
  injection same with finEq bytesEq
  subst finEq
  rw [bytesEq] at consumed
  have liqEq : liqTyped.toB256 = liq'.toB256 :=
    mint_encodeWord_inj (bytesTyped.symm.trans bytesEq)
  have shape := mintAfterFee_finished_shape typedEq
  have dPost : post = d := Outcome.halted.inj halted
  subst dPost
  -- the fee branch's actual post
  have sourceResult := observation.sourceResult
  have feePostEq := Outcome.returned.inj observation.returned
  rw [observation.last, dEq, outEq] at feePostEq
  rw [dEq, outEq] at sourceResult
  obtain ⟨accept, _, _, _, logsDisj⟩ := sourceResult
  have baseLogs : (feeKLastWorld sevm dF).logs = b.logs := by
    rw [feeKLastWorld, afterSload_logs, postF.logs, feeFactoryCallWorld,
      temporalAccountAccessBase_logs, feeFactoryLoadWorld, afterSload_logs, logs1]
  rw [← feePostEq] at logsDisj
  have feeLogsFact : ∃ feeLogs : List Log, feePost.logs = b.logs ++ feeLogs ∧
      (((feeBranchSourceFee { current.state with unlocked := 0 } sevm (feeKLastWorld sevm dF)
          (Bytes.toB256 (outF.take 32))
          (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
          (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))).events = [] ∧
          feeLogs = []) ∨ ∃ L : B256, L ≠ 0 ∧
        (feeBranchSourceFee { current.state with unlocked := 0 } sevm (feeKLastWorld sevm dF)
          (Bytes.toB256 (outF.take 32))
          (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
          (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))).events =
          [.transfer 0 (Bytes.toB256 (outF.take 32)).toAdr L] ∧
        feeLogs = [lpMintRawLog sevm.currentTarget (Bytes.toB256 (outF.take 32)).toAdr L]) := by
    rcases logsDisj with ⟨events, feeLogsEq⟩ | ⟨L, nonzero, events, feeLogsEq⟩
    · exact ⟨[], by rw [feeLogsEq, baseLogs, List.append_nil], Or.inl ⟨events, rfl⟩⟩
    · exact ⟨_, by rw [feeLogsEq, baseLogs], Or.inr ⟨L, nonzero, events, rfl⟩⟩
  obtain ⟨feeLogs, feePostLogs, feeLogsShape⟩ := feeLogsFact
  rw [natCache0, natCache1] at accept
  rw [cache0, cache1] at accept feeLogsShape logsTyped
  have keysSub : ∀ k, keys k → WriterExtend K (mintTraceKeys root) k := by
    rw [keysEq]
    intro k tracked
    split at tracked
    · rcases tracked with (old | zeroRow) | toRow
      · exact mint_feeKeys_sub sub feeRow _ _ _ _ _ k old
      · exact mint_single_row rows.1 k zeroRow
      · rw [toAdr_toB256] at toRow
        exact mint_single_row rows.2 k toRow
    · rcases tracked with old | toRow
      · exact mint_feeKeys_sub sub feeRow _ _ _ _ _ k old
      · rw [toAdr_toB256] at toRow
        exact mint_single_row rows.2 k toRow
  rw [cache0, cache1, toAdr_toB256, feePostLogs] at logs
  rw [liqEq] at logsTyped
  have codeF : ((feeFactoryCallWorld sevm d1).getCode current.state.factory).size ≠ 0 := by
    rw [feeFactoryCallWorld, mint_tAAB_getCode, ← factoryTarget]
    exact mint_size_ne observation.code
  refine ⟨value, nonstatic, out0, out1, outF,
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, call0', post0.returnData,
      by rw [mint_tAAB_getCode, ← token0Target]; exact mint_size_ne code0,
      call1', post1.returnData,
      by rw [mint_tAAB_getCode, ← token1Target]; exact mint_size_ne code1,
      callF', postF.returnData, codeF⟩, ?_⟩
  intro balance0 balance1 feeTo
  refine ⟨views0, views1, viewsF, finished,
    staticViewChildReturns (mintSourceLockedFrame current ctxM recipient)
        (requestFor .mintBalance0 current.state.token0 (.balanceOf ctxM.pair)) 0 views0 ++
      (staticViewChildReturns ((mintSourceLockedFrame current ctxM recipient).beginResume
          (requestFor .mintBalance0 current.state.token0 (.balanceOf ctxM.pair)))
          (requestFor .mintBalance1 current.state.token1 (.balanceOf ctxM.pair)) 0 views1 ++
        (staticViewChildReturns (mintSourceFeeFrame current ctxM recipient)
          (requestFor .mintFeeTo current.state.factory .feeTo) 0 viewsF ++ [])),
    keys, liq', _, feeLogs, _, consumed,
    shape.1, shape.2.1, shape.2.2, keysSub, wrep, accept, feeLogsShape, logs, logsTyped,
    ⟨_, by rw [logs]; simp only [List.append_assoc]; rfl, mint_logs_raw feeLogsShape⟩,
    output, ?_, ?_, ?_, ?_⟩
  · intro picked member
    rcases List.mem_append.mp member with left | right
    · rcases List.mem_append.mp left with first | second
      · exact ⟨(auth0 picked first).2.2.2.2.2.1, (auth0 picked first).1,
          (auth0 picked first).2.2.2.1⟩
      · exact ⟨(auth1 picked second).2.2.2.2.2.1, (auth1 picked second).1,
          (auth1 picked second).2.2.2.1⟩
    · exact ⟨(authF picked right).2.2.2.2.2.1, (authF picked right).1,
        (authF picked right).2.2.2.1⟩
  · rcases prov0 with ⟨empty, native⟩ | derived
    · exact Or.inl ⟨empty, token0Target ▸ native⟩
    · exact Or.inr derived
  · rcases prov1 with ⟨empty, native⟩ | derived
    · exact Or.inl ⟨empty, token1Target ▸ native⟩
    · exact Or.inr derived
  · rcases provF with ⟨empty, native⟩ | derived
    · exact Or.inl ⟨empty, factoryTarget ▸ native⟩
    · exact Or.inr derived

end Blanc.Lift.UniswapV2Pair
