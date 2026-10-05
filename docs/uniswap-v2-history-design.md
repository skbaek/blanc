# Uniswap V2 pair: configured-history theorem — design and frozen statements

Scratch design for goal `uniswap-v2-pair-bytecode-v1` (U2(b), U3/U5/U7 at history level).
Branch `claude/uv2-history-ladder`, based on integration commit 00f12c48. To be deleted or folded
into the claim map / COMMON_API at integration. Everything below marked **(proved)** elaborates in
`Blanc/ExecutionWholeFrameAccounting.lean`; every other Lean block is a *frozen statement*, not yet
proved, and appears only here.

## 1. Verdict on the obstacle

The master's reading of `SpawnReplay` is correct: it asks that the frame's own carrier effect be
complete at its first external instruction, with only silent steps afterwards. Every pair entry
with an external instruction violates it: `mint` and `sync` write after their `STATICCALL`s;
`burn` writes (fee mint, `_burn`), `CALL`s two transfers, `STATICCALL`s two balances, then writes
reserves/oracle/`kLast`/unlock; `swap` and `skim` `CALL` first and write after.

The proposed repair (commute the frame's post-call suffix with the children's carrier effect) is
**not needed, and would be the more expensive route**, because the pair's frame theorems already
consume the frame's *whole subtree*:

* every calling-entry frame theorem concludes `ExactConsumes (startTyped current ctx entry) T out`
  together with `WriterRep K' (post.getStor pair) out.frame.current.state`, where `T` carries the
  re-entered pair frames as nested `.invoke` turns (`SwapCanonicalBody` in
  `SwapCanonical.lean`: `mutableTranscript turns0/turns1/turnsC`, with `SwapCallProvenance`;
  `MintCanonicalResult` in `MintCanonical.lean`; `BurnEntryFinished` in `BurnFeeTransfers.lean`;
  sync, skim likewise);
* the re-entered frames are consumed through `lockedPairSupply` (`LockedSupply.lean`), which
  dispatches every one of the 27 selectors of a re-entered pair frame: the lock-guarded ones
  cannot succeed (`pair_lockGuarded_unlocked`), the ERC-20 writers, `initialize`, `permit` and the
  views are each one exact invocation (`LockedAuth`).

So the post storage of a successful pair frame already represents the model run of that frame
*including* its re-entered pair children. A WETH9-style replay "own step, then settled children"
would replay those children twice; avoiding that would need either new frame proofs over flat
transcripts or a model-level commutation theorem over the mutual `drive`/`driveTurns` fuel
recursion (estimated 2–4M tokens, no reuse). The cheaper and exactly-faithful route is a generic
**whole-frame** handler: a non-static target frame's replay is one step covering its subtree, and
its observation is the list of all committed pair frames below it.

### Reuse of previous masters' route

| Piece | Verdict |
|---|---|
| Frame theorems (`*_bytecode_exact_consumes`, `burnRaw_source_finished`) and nested-turn machinery (`MutableTurns`, `LockedSupply`, `PairFrameSupply`/`PairFrameOutcome`, `*Provenance`) | **Reused as is.** `PairFrameSupply` is exactly the shape of the per-frame obligation below. |
| `SourceReplay`, `PairStorageReplay` (+ `append`, `model_laws`), `runSourceInvocations` | **Reused as is**: the carrier's replay relation. |
| `HistoryStep`, `historyReplayCarrier`, `historyObservation` (`HistoryReplay.lean`) | **Reused with one change**: the ladder hands the handler a frame, not a `LocatedFrame` path, so the step is anchored at `Exec.Frame` (context path `[]`; the path only labels log receipts, never state). The step also gains an authentication conjunct (§3). |
| `approve/transfer/transferFrom/initialize_history_replay`, `noncalling_history_replay`, `selected_*` | Superseded by the per-frame supply (§4, W4); delete or fold (leaf ⇔ valuable). |
| `retainedTargetTurns*`, `SegmentedHistory`, `CursorCuts/CursorExact`, `ExecFreeUntil` | Not needed for the history theorem: the ladder's committed-frame observation replaces the outermost-target-frame extraction. They stay only where frame proofs already use them. |

## 2. Generic extension — `Blanc/ExecutionWholeFrameAccounting.lean` (all proved, committed)

```lean
def Exec.derivEntry (P : Exec.Deriv → Prop) (sevm : Sevm) (pre : Devm) : Prop :=
  ∀ (out : Execution) (run : Exec 0 sevm pre out), P ⟨0, sevm, pre, out, run⟩

theorem Exec.derivEntry_of_run {P} {sevm pre out} (exc : Exec 0 sevm pre out)
    (h : P ⟨0, sevm, pre, out, exc⟩) : Exec.derivEntry P sevm pre            -- (proved)
theorem Exec.derivEntry_of_deriv {P} {D : Exec.Deriv} (pc : D.pc = 0) (h : P D) :
    Exec.derivEntry P D.sevm D.devm                                          -- (proved)

theorem Exec.CoreAccounting.staticObservedNil (kinds : SpawnKinds ca sem) … (deeper : …) :
    ∀ run, ParentPrefix root ⟨pc, sevm, d, out, run⟩ → sevm.isStatic = true →
      (Exec.descendantFrames run).flatMap V.frameObs = []                     -- (proved)

def Exec.CoreAccounting.WholeFrameReplay (ca sem entry) (C : ReplayCarrier ca)
    (V : ReplayObservation C) : Prop :=
  ∀ {sevm pre post} (run : Exec 0 sevm pre (.ok post)),
    sem.Run sevm pre post → sevm.currentTarget = ca → CoveredFork sevm.benvStat.fork →
    sem.At ca 0 sevm pre → Exec.FrameAdmitted ca entry run → sum pre.state.bal < 2 ^ 256 →
    sevm.isStatic = false →
    ∃ steps, C.Replay (C.frameEntry sevm pre.state) steps (C.ofState post.state) ∧
      V.obs steps = (Exec.committedFrames run).flatMap V.frameObs

theorem Exec.CoreAccounting.wholeFrameTarget (entryOfState) (ofStateGet) (obsStatic)
    (kinds : SpawnKinds ca sem) (whole : WholeFrameReplay ca sem entry C V) (hrun) (target)
    (deeper) : Exec.CoreAccounting ca sem entry C V 0 sevm pre (.ok post)     -- (proved)

def ExecutionAccountingReplay.wholeFrameLadder (C V append tag frameTag entryOfState ofStateGet
    obsStatic obsForeign kinds whole preserves) : AccountingLadderAdmitted c ca entry  -- (proved)
```

`derivEntry` answers a gap the pair hits immediately: `Exec.FrameAdmitted` attaches an entry
condition on `(sevm, pre)` only, but some pair rows are selected by a callee's *answer*
(`mintFeeReplyKeys root`: the `balanceOf[feeTo]` row). Because `Exec` is deterministic and
subsingleton (`Exec.result_unique`, `Exec.unique`), a condition on the frame's own derivation is
an entry condition. No change to `FrameAdmitted` or to the ladder.

Dedup note: `staticObservedNil` restates the private `staticChain` of
`ExecutionModelAccounting.lean` (the duplication gate passes; it is a concept duplicate). Fold at
integration by making that one public under this name and deleting the copy here; it was not done
now because `ExecutionModelAccounting` is imported by `Lift/ReachChain` and every lift above it.

## 3. Headline statements (frozen, unproved)

Namespace `Blanc.Lift.UniswapV2Pair`. New pair-side definitions:

```lean
/-- The certified pair runtime as a code semantics (cf. `weth9Sem`). -/
def pairSem : CodeSem          -- image := some code.toList; Run sevm _ _ := sevm.code = code

/-- Storage-only frame contract over a trace universe `U`. -/
def pairSpec (U : WriterKey → Prop) : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly pairSem
    (fun s => ∃ st K, (∀ k, K k → U k) ∧ WriterRep K s st)

/-- Rows one actual pair frame selects: its decoded mapping rows, static-view rows, and the
rows its own execution selects (mint/burn recipients, `balanceOf[pair]`, the fee-reply row). -/
noncomputable def pairFrameKeys (D : Exec.Deriv) : List WriterKey

/-- HASH-T rows of a history: every raw pair frame root, rolled-back ones included. -/
noncomputable def pairHistoryTouchedKeys (pair : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List WriterKey :=
  trace.rawFrames.flatMap fun D =>
    if D.sevm.currentTarget = pair then pairFrameKeys D else []

def pairEntry (U : WriterKey → Prop) : Sevm → Devm → Prop := fun sevm pre =>
  Exec.FreshEntry sevm pre ∧ pre.output = [] ∧ sevm.data.length < 2 ^ 256 ∧
    Exec.derivEntry (fun D => ∀ F ∈ Exec.rawFrameRoots D.exc,
      F.sevm.currentTarget = sevm.currentTarget → ∀ k ∈ pairFrameKeys F, U k) sevm pre

/-- One outermost committed pair frame with the invocation that consumes it and every pair frame
re-entered below it. -/
structure PairStep where
  frame : Exec.Frame
  entry : Entry
  transcript : Transcript

def PairStep.source (s : PairStep) : SourceInvocation :=
  { context := writerContext s.frame.sevm [], entry := s.entry, transcript := s.transcript }

/-- The committed non-static pair frames of a frame's subtree, in execution order. -/
def pairSubtreeFrames (pair : Adr) (f : Exec.Frame) : List Exec.Frame :=
  (Exec.committedFrames f.run).flatMap (pairFrameObservation pair)

def committedPairFrames (pair : Adr) (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    List Exec.Frame :=
  trace.settledFrames.flatMap (pairFrameObservation pair)

/-- The entry is the one the frame's calldata decodes, and the transcript is the one its actual
external calls answered: the per-family provenance the frame theorems already state
(`SwapCallProvenance`, `SwapBalanceCall`, `MintObservedSteps`/`MintViewProvenance`,
`SkimFirstSteps`/`SkimSecondSteps`, the sync balance calls, `LockedAuth`, and the Burn queue
provenance still owed, §5 G4). -/
def PairStep.Authentic (pair : Adr) (s : PairStep) : Prop :=
  s.frame.sevm.currentTarget = pair ∧ s.frame.sevm.isStatic = false ∧
    PairFrameAuth s.frame.rootDeriv s.entry s.transcript
```

**U2(b) — the headline** (shape of `weth9_history_committed`; premises CODE, INIT, HASH-T only;
no token premise):

```lean
theorem pair_history_committed {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    some (future.state.getCode pair).toList = pairSem.image ∧
    ∃ steps : List PairStep,
      steps.flatMap (fun s => pairSubtreeFrames pair s.frame) = committedPairFrames pair trace ∧
      (∀ s ∈ steps, s.Authentic pair) ∧
      ∃ (finish : State) (K' : WriterKey → Prop),
        SourceReplay st₀ (steps.map PairStep.source) finish ∧
        runSourceInvocations st₀ (steps.map PairStep.source) = some finish ∧
        (∀ k, K₀ k → K' k) ∧
        (∀ k, K' k → WriterExtend K₀ (pairHistoryTouchedKeys pair trace) k) ∧
        WriterRep K' (future.state.getStor pair) finish
```

Reading: the list `steps` is not free. Its flattened observation is *every* settlement-committed
non-static pair frame of the trace in trace order (rolled-back frames are absent; static frames
observe nothing), each step's head is a committed non-static pair frame, and each step's entry and
transcript are authenticated against that frame's actual run. Each step's frame is therefore an
outermost one: a re-entered pair frame lies in exactly one step's subtree and is consumed inside its
parent's transcript (the WETH9 "re-entered call after its sender" precedent, here inside the
parent). The future storage represents the model fold `runSourceInvocations` from the checkpoint
state. Token answers enter only through the authenticated transcripts.

**INIT corollary** (`InitializedCheckpoint` = `WriterRep ⊥ s (initializedState …)`, from U8):

```lean
theorem pair_history_initialized … (initial : InitializedCheckpoint
      (checkpoint.state.getStor pair) factory domain token0 token1)
    (fresh : WriterFreshKeys (fun _ => False) (pairHistoryTouchedKeys pair trace)) : … -- same
    -- conclusion with st₀ := initializedState factory domain token0 token1, K₀ := ⊥
```

**U7 ledger corollary** (`SourceReplay.ledger`): add `(ledger : st₀.Ledger)` and conclude
`finish.Ledger` with the representation above (from the initialized checkpoint, `ledger` is
proved, not assumed: every balance and the supply are zero).

**U5 oracle corollary** (`SourceReplay.oracle_mod`; the timestamp is `sevm.benvStat.time` of
the frame's block via `writerContext`):

```lean
  finish.price0CumulativeLast.toNat =
    (st₀.price0CumulativeLast.toNat +
      oracleSum0 (sourceReplayUpdates st₀ (steps.map PairStep.source))) % 2 ^ 256 ∧ (sym. 1)
```

**U3 share-value corollary** (fee off, `NoShrink` as a named per-frame ENV premise about the
authenticated answers; never a model premise):

```lean
/-- Burn and sync frames: each final `balanceOf(pair)` answer is at least the reserve stored at
the frame's entry. Other entries: `True` (as `EntryNoShrink`). -/
def PairStepNoShrink (pair : Adr) (s : PairStep) : Prop
/-- Mint and burn frames: the factory answered `feeTo = 0`. -/
def PairStepFeeOff (s : PairStep) : Prop

theorem pair_history_feeOff_product … (as headline) …
    (feeOff : ∀ s : PairStep, s.Authentic pair → PairStepFeeOff s)
    (noShrink : ∀ s : PairStep, s.Authentic pair → PairStepNoShrink pair s) :
    … ∧ ∀ before after,
      (before, after) ∈ sourceReplayEdges st₀ (steps.map PairStep.source) →
      0 < before.totalSupply.toNat →
      before.reserve0.val * before.reserve1.val * after.totalSupply.toNat ^ 2 ≤
        after.reserve0.val * after.reserve1.val * before.totalSupply.toNat ^ 2
```

Edges are per outermost step; a re-entered ERC-20 child changes neither reserves nor supply, so
no edge is lost. The fee-on exact form is `runTyped_mint/burn_feeOff_product`'s fee-amount variant
lifted the same way.

## 4. Per-entry obligations and what discharges them

Instantiate `wholeFrameLadder` with `C := pairStepCarrier pair U` (`Snap := Stor`,
`Replay a steps b := PairStorageReplay U a (steps.map source) b ∧ ∀ s ∈ steps, s.Authentic pair`),
`V` with `frameObs := pairFrameObservation pair`, `obs := flatMap (pairSubtreeFrames pair ∘ frame)`,
`entry := pairEntry U`, `U := WriterExtend K₀ (pairHistoryTouchedKeys pair trace)`.

| Obligation | Discharged by | State |
|---|---|---|
| `entryOfState`, `ofStateGet`, `obsStatic`, `obsForeign`, `append`, carrier laws | definitional (`PairStorageReplay.append`, `pairFrameObservation`) | trivial |
| `SpawnKinds pair pairSem` | `CursorOK.exec_call_or_staticcall` on `cert_check` (as `weth9_spawnKinds`) | trivial |
| `(pairSpec U).PreservesAdmitted pair (pairEntry U)` via `preserves_inv_admitted` | per-frame supply (W4) for non-static frames; `Exec.storageView_committedPost_eq_of_static` for static ones | W5 |
| `WholeFrameReplay pair pairSem (pairEntry U) C V` | per-frame supply (W4) with `steps := [⟨Exec.Frame.ofRun run committed, entry, T⟩]`; the observation equality is `rfl` by the choice of `obs` | W6 |
| trace admission `trace.FrameAdmitted pair (pairEntry U)` | `frameAdmitted_iff_rawFrames` + `freshFrameAdmitted` + `frameAdmitted_calldata` + `Exec.derivEntry_of_deriv`; output-empty at roots (G2) | W2 |
| `StateInv` at the checkpoint | `installed`, `initial.extend fresh` (`WriterRep.extend`) | W7 |

**The per-frame supply (W4)** — the unlocked analogue of `lockedPairSupply`:

```lean
theorem pairSupply {U : WriterKey → Prop} (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList) (pair : Adr) :
    PairFrameSupply pair (fun st s => ∃ K, (∀ k, K k → U k) ∧ WriterRep K s st)
      (fun D => ∀ F ∈ Exec.rawFrameRoots D.exc,
        F.sevm.currentTarget = D.sevm.currentTarget → ∀ k ∈ pairFrameKeys F, U k)
      PairFrameAuth pairOwnedRaw
```

dispatching `pair_bytecode_selector_inv`'s 27 selectors:

| Selectors | Frame theorem | Gap |
|---|---|---|
| `swap` | `swap_bytecode_exact_consumes` | none (HASH-T from `swapTraceKeys ⊆ pairFrameKeys`-union, G3) |
| `mint` | `mint_bytecode_exact_consumes` | none |
| `sync` | `sync_bytecode_exact_consumes` | none |
| `skim` | `skim_bytecode_exact_consumes` | none |
| `burn` | `burnRaw_source_finished` (needs `K (.balance pair)`: extend `K` by it, fresh from `U`) | **G4: transcript provenance** (`BurnEntryFinished` has `∃ nested` with no provenance — "queue occurrence attachment is a separate canonical obligation") |
| `transfer`, `approve`, `transferFrom`, `initialize`, `permit`, 15 views (non-static) | the private `locked_*_outcome` of `LockedSupply.lean` | **G5: lock-agnostic variants** (they take `st.unlocked = 0`; the underlying frame theorems do not care) |

No existing frame theorem *statement* changes. Changes elsewhere: `HistoryStep` → `PairStep`
(frame-anchored, authenticated), `historyReplayCarrier`/`historyObservation` adapted, the
single-frame `*_history_replay` family deleted once superseded; `mintSourceContext` and
`writerContext` are the same definition and should be unified (normalization by `rfl`).

## 5. Gaps and remaining units, with cost estimates

Token estimates are worker tokens for an Opus-class worker on this repo (calibration: 3Crv 3.3M
whole goal; WETH9 history 3 files ≈ 0.4k lines).

| Unit | Content | Est. size | Est. tokens |
|---|---|---|---|
| W1 | `pairSem`, `pair_spawnKinds`, `pairSpec`, `StateInv` iff | ~120 lines | 0.2–0.3M |
| W2 / **G2** | `pairFrameKeys`, `pairHistoryTouchedKeys`, `pairEntry`; trace admission; *generic* "every retained raw frame root has empty output" (mirror of `ExecutionTraceFresh` using `Frame.enter_run_output_empty`; or add `output` beside `FreshEntry` in a new predicate) | ~250 lines (≈150 generic) | 0.4–0.6M |
| W3 / **G3** | `swap/skim/mint/sync/burn` trace-key lists ⊆ union of `pairFrameKeys` over `rawFrameRoots`; `LockedGood`/`staticGood` from admission | ~150 lines | 0.2–0.3M |
| W4 | `pairSupply` dispatcher + `PairFrameAuth` (disjunction of the families' provenance) | ~400 lines | 0.8–1.2M |
| **G4** | Burn transcript provenance (balance/fee/transfer answers and nested turns tied to the actual calls) — in flight on the burn lane (70a9cc68, 2f27d70d) | ~600–1000 lines | 1–2M (uncertain) |
| **G5** | Lock-agnostic writer/permit/view outcomes (generalise the private `locked_*_outcome`) | ~150 lines | 0.3M |
| W5 | `pairSpec_soundAdmitted` / `PreservesAdmitted` | ~80 lines | 0.15M |
| W6 | `PairStep` carrier/observation, `pair_wholeFrameReplay` | ~150 lines | 0.3M |
| W7 | `pair_history_committed`, INIT corollary | ~150 lines | 0.3–0.4M |
| W8 | U3/U5/U7 corollaries; `PairStepNoShrink/FeeOff` → `sourceReplayAnswers` bridge (positions `firstWord`/`ownTail` against `PairFrameAuth`) | ~250 lines | 0.4–0.6M |
| W9 | Cleanup: delete superseded `History*` single-frame theorems, fold `staticObservedNil` dedup, `mintSourceContext` unification | — | 0.1–0.2M |

Total ≈ 4–6.5M tokens, of which G4 is the only large unknown. Critical path: G4 ∥ (W1–W3, G5)
→ W4 → W5/W6 → W7 → W8. Everything except W4's burn arm and W8's burn edges can proceed before
G4 lands.

## 6. Risks

1. **G4 (burn provenance)** is the long pole: without it the burn steps' transcripts are
   existential, so the U3 burn edges would rest on an unauthenticated answer. Do not ship the U3
   corollary with an unauthenticated burn arm.
2. **G5 may not be a pure generalisation** if any `locked_*_outcome` proof uses `unlocked = 0`
   beyond `LockedRep`; the view and ERC-20 frame theorems underneath take an arbitrary state, so
   the risk is low.
3. **Authentication uniqueness.** The U3 premises quantify over *all* authenticated steps, so they
   are honest whether or not `PairFrameAuth` is functional; a uniqueness lemma is not required. If a
   reviewer wants the list stated "definitionally" (as WETH9's `committedInvocations`), that needs a
   functional transcript extractor from `Exec` — not planned; the observation equality already pins
   the frames.
4. **Elaboration cost of the 27-way dispatcher**: `lockedPairSupply` shows it is feasible in one
   proof; keep each arm a one-line call.
5. **Generic file placement**: `ExecutionWholeFrameAccounting` imports `ExecutionModelAccounting`
   (for `Exec.descendantFrames_flatMap_runOk`); fine now, revisit at the dedup fold.
6. Pre-existing, not from this branch: `scripts/GATES.md` module counts (980/978/977) lag the
   integration tree (1176/1174/1173); `check-doc-counts.sh` is red on 00f12c48 already.

## 7. Decisions for the master (within §10 authority; no user packet)

**D1 — replay granularity.** Recommended: outermost committed pair frames as steps, re-entered pair
frames consumed in their parent's transcript, observation = every committed pair frame (this
design). Alternative: one step per committed pair frame (WETH9 flat order) — needs a model-level
commutation theorem over `drive` or re-proved frames without nested turns (+2–4M tokens, discards
the nested-turn machinery). Cost of waiting: none for W1–W3/G5; W4 shape depends on it.

**D2 — `NoShrink` form.** Recommended: per-frame ENV premise over authenticated steps
(`PairStepNoShrink`: final `balanceOf(pair)` answers ≥ reserve stored at the frame's entry), as in §3.
Alternative: a trace-level predicate over the actual `STATICCALL` child frames' outputs, bridged to
the step form (+0.3M tokens, same strength).

## 8. Implementation status (W1–W8; G4 merged, burn arm wired)

Proved in `Blanc/Lift/UniswapV2Pair/PairSupply.lean` and `PairHistory.lean` (generic:
`Blanc/ExecutionTraceEntered.lean`). Deviations from §3–§4, all within the accepted D1/D2:

* **Carrier.** `Snap` is the storage *view* `(getStor pair).get`, not `Stor`: raw `Stor` equality is not
  a function of the words, so `ofStateGet` fails for `Stor`. Representations move along views by
  `WriterRep.congr`.
* **Steps are frames; invocations are produced per incoming state.** The carrier's `Step` is
  `Exec.Frame` and `PairReplay` says: from every incoming representation, there are authenticated
  `PairStep`s over exactly these frames that `SourceReplay` from that state. The supply's transcript
  existentials sit under the model state (`∀ st, ∃ transcript`), so a `PairStep` list cannot be fixed
  before the state; the headline fixes `st₀` first, so its statement is unchanged.
* **`WholeFrameReplay` takes the frame's commit proof**, so the step names the committed frame.
* **`PairStep.Authentic`** adds `pc = 0` and an explicit commit conjunct (correction 1).
* **Burn arm.** `BurnAuth` (decoded `.burn recipient` and G4's `BurnFrameAuth`), produced by
  `pair_burn_outcome` from `burnRaw_source_authentic` (G4, merged from `claude/uv2-burn-provenance`
  0e4e7257); `K` is extended by the Pair's own LP row first. No history theorem has a burn premise.
* **HASH-T rows.** `pairHistoryTouchedKeys` collects `pairDerivKeys D` (the rows of every Pair frame
  entered below each raw Pair root), selector-independent; `pairFrameKeys` adds `.balance pair` (burn).
* **U3** is `pair_history_feeOff_product`, with `sourceReplayAnswers st₀ (steps.map source)` inside the
  existential (correction to §3); U5 `pair_history_oracle`, U7 `pair_history_ledger`.
* **Not done (W9):** the superseded `HistoryReplay`/`HistoryWriters`/`HistoryWriterCheck`/
  `HistoryWriterWalk` family still builds (its `pairFrameObservation` is distinct from the new
  `pairFrameObs`); deleting it orphans `Lift/ReachDispatch` (proof-recipe registered). The private
  `locked_*_outcome` of `LockedSupply` are concept duplicates of `free_*_outcome`; `staticObservedNil`
  and `mintSourceContext` folds as in §2/§4.

## 9. History liveness (U6) and fee-on (U3) — status

`Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean`: `PairHistoryReplayed`/`pair_history_replayed` package
the headline's existential; `pair_live_outcome` is the shared glue (a pc-zero run at the future world
plus HASH-T freshness of its own `pairDerivKeys` gives `PairStepOutcome` from `finish`). Instances:
`pair_history_writer_live` (transfer/approve/transferFrom, cost `writer.cost`),
`pair_history_sync_live` (cost `syncCalleePrefixGas … + 244`), `pair_history_mint_live`
(`env.gas + 228`), `pair_history_swap_live` (both callback shapes; `swapFrontTransferGas … +
swapPrefixGas … + 445`, `SwapSafeTransferForward` a named premise). Skim and burn instances are one
`pair_live_outcome` call each once their forward theorems land. Model-acceptance bridges: writers
(`startImmediate` at `finish`), sync (`finish.unlocked = 1` and `State.update` accepting the answers,
`State.update_bounds`), swap (`SwapModelConditions` at the actual post-callback answers; the back half's
input guard, `K` facts and bounds from `swapCheck_raw`, `SwapBackCalleeEnv` in `SwapForwardAccept.lean`),
mint (`MintModelConditions` at the actual token and `feeTo` answers; the lock word, bounds, cover, fee
guards and pricing facts from `MintPrefixCallee.accepted` in `MintForwardAccept.lean`, with HASH-T
freshness of the address-zero, recipient and `feeTo` LP rows). Every callee environment now carries
only callee answers, returned gas, charge equations and residual sentries. U3 fee-on: `SourceReplay.feeOn_product`,
`pair_history_feeOn_product`.
