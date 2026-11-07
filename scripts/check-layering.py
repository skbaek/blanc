#!/usr/bin/env python3
"""Import-hierarchy gate: Blanc's contracts must stay siblings.

Enforces the rule stated in README.md, "Module hierarchy: contracts are
siblings" -- every contract's program, compiled-bytes and property modules sit
at the same level of the import hierarchy, and no contract's module imports
another contract's, in either direction, at any layer.

Seven checks, all falsifiable, all exercised by negative controls:

  1. Classification is total. Every Lean module in the repository appears in
     the table below, wherever it sits in the tree -- discovery is recursive
     precisely so a module cannot escape by moving into a subdirectory. An
     unclassified module FAILS the gate rather than being skipped -- otherwise
     contract #3 could be added and silently escape the rule, which is the
     vacuity this gate exists to prevent.
  2. No cross-contract import. A contract module importing a module owned by a
     different contract is the defect the rule names: the imported thing was
     never that contract's property, and belongs upstream.
  3. No inverted import. A shared module importing a contract module would put
     an upstream layer below a contract -- the same break, other direction.
  4. The composition stratum is strictly downstream. A `Blanc/Composition/*`
     module is the one place a theorem may name two or more contract families
     at once. Each COMPOSITION entry declares its contract families: it may
     import shared modules, those families, and compositions whose declared
     families are a subset of its own. Declarations fail closed on malformed,
     empty, duplicate or unknown families; total classification rejects a
     missing entry. The relation is one-way: no shared module and no contract module may import
     composition, and composition may not import a root. Roots aggregate
     composition, never the reverse.

  5. A shared facility that an active proof recipe owns is reachable from the
     need-first registry. `docs/COMMON_API.md` is the entry point an author is
     told to consult before writing a contract-local helper, and
     `scripts/proof-recipes.toml` is what `blanc_suggest` reads; a
     contract-neutral module named by one and not the other is a facility that
     exists without being findable, which is the defect S8 names. So every
     active recipe whose `owner_module` this table classifies SHARED must have
     its module path cited in `docs/COMMON_API.md` (missing entry), and every
     `Blanc/*.lean` path `docs/COMMON_API.md` cites must exist on disk (stale
     entry). Both directions fail closed, and both populations are non-empty by
     assertion, so a registry or a registry section reworded out of this
     check's sight FAILS rather than passing green over nothing.

     This check is deliberately narrow. It asks whether a shared facility with
     a recipe has a registry entry at all; it does not judge whether the entry
     is a good one, and it is not a similarity detector over the corpus. It
     lives here because the SHARED classification below is the repository's own
     statement that a module is contract-neutral and reusable, and that is
     exactly the population the obligation attaches to.

  6. Every module classified SHARED is reachable from the need-first registry.
     Check 5 attaches its obligation to the *recipe* population, so a shared
     facility that owns no recipe escapes it entirely: `Blanc/SymbolicProgram.lean`
     shipped as a 1,091-line SHARED module with no `docs/COMMON_API.md` entry
     and no recipe, and check 5 reported green over it because it had nothing
     to bind. That is the gap this check closes. The SHARED classification in
     the table below is the repository's own statement that a module is
     contract-neutral and reusable; the discovery obligation therefore attaches
     to that statement directly, not to whether someone also wrote a recipe.

     A shared module satisfies this check when `docs/COMMON_API.md` cites its
     path inside the need-first tree: the Root section or a need section
     (`## E — ...` through `## C — ...`), outside fenced code. A citation only
     in the preamble, the closing workflow, or a tail appended below every
     need branch does not count, because no branch leads to it (check 5's
     missing-entry direction uses the same rule; its stale-entry direction
     still reads every citation). The only other way out is `DISCOVERY_EXEMPT` below, which names each
     unreachable shared module together with the concrete reason it is not a
     facility an author could be told to find -- a compatibility re-export that
     declares nothing, the registry's own machinery, or a negative-control
     fixture. That table is checked in both directions: an exemption for a
     module that is no longer shared, no longer present, or now cited FAILS, so
     it prunes itself and cannot quietly absorb the next shipped facility.

     Note what this check is not. It does not require a recipe (step 5 of
     `docs/COMMON_API.md`'s own workflow makes a recipe conditional on a
     reliable goal shape existing), it does not judge the quality of an entry,
     and it is not a similarity detector: it binds exactly the
     SHARED-registration-to-registry-entry relation and nothing else. An
     ordinary edit to a shared file that is already cited is unaffected.
  7. The generated shared-module inventory is current. `docs/MODULE_INVENTORY.md`
     lists every SHARED module with its own header summary and the registry
     branches citing it; `scripts/generate-module-inventory.py` renders it from
     this table, the modules' headers and `docs/COMMON_API.md`, and the gate
     byte-compares the committed file with that rendering. A hand edit, a new
     or reclassified shared module, a changed module summary, or a moved
     registry citation without `--write` FAILS.

Roots (Blanc.lean, Main.lean) exist to import everything and are exempt from 2,
3 and 4 as importers, never from 1, and are outside 5, 6 and 7.

Check 4 is what keeps 2 honest once a cross-family theorem exists: without an
explicit downstream stratum the only ways to state one are an inverted import,
a cross-contract import, or hiding it in a root, and the third is invisible to
this gate by construction.

Needs no Lean toolchain, no build and no network: it reads committed .lean
files only, so it runs identically here and in CI.

Import recognition is intentionally limited to Lean's module header.  It follows
the Lean 4.32.1 header grammar: optional `module` and `prelude` directives,
then `public? meta? import all? identWithPartialTrailingDot` commands.  The
reader handles nested comments, quoted identifier components, and whitespace
across physical lines; it stops at the first non-header command.  An
unterminated header block comment or string, an incomplete trailing-dot name,
or a semantically disallowed modifier combination fails the gate closed rather
than producing a partial import list.

Usage: scripts/check-layering.sh [--root DIR]

--root overrides the repository root (default: the parent of scripts/). It
exists so a negative control can point the gate at a mutated copy of the tree
without touching the committed one.

CLI contract: exit 0 if and only if the gate passes; output ends with one
unambiguous verdict line.
"""

import os
import re
import sys
import tomllib

# ---------------------------------------------------------------------------
# The module classification. This is the part no script can infer, so it is
# stated here; ADDING A CONTRACT MEANS ADDING A LINE TO `CONTRACTS`, and that
# is the moment the rule starts binding it. Module names are as written in
# `import Blanc.X`; `Blanc.lean` itself is spelled "Blanc".
#
# Deliberately hardcoded rather than read from a committed manifest file: one
# file, no data/code drift. If a future contract makes this table unwieldy,
# lifting it back out to `scripts/contract-modules.txt` is a small change.
# ---------------------------------------------------------------------------

SHARED = ["Basic", "BytePattern", "Semantics", "HistoricalFork", "CommonCore", "MachineDataFacts", "RlpConcrete", "RlpListEncode", "RlpBytesInjective", "RlpRoundTrip",
          "ProofRecipesGenerated", "ProofRecipeTactic", "Tactics", "CommonProofs.Base", "CommonProofs.Frames", "CommonProofs.MemImage", "CommonProofs.Messages", "CommonProofs.Walk", "CommonProofs.Hinv", "CommonProofs.NoDel", "CommonProofs.Balance", "Ladder", "BalanceAlgebra", "LedgerConservation", "StorageOnlySpec", "SlotFootprint", "FakeExponential", "FakeExponentialGrowth", "FakeExponentialEval", "WordFakeExponential", "WordFakeExponentialBound", "WordFakeExponentialEval", "FakeExponentialWordCorrespondence", "FakeExponentialWordDomain", "WordArithmetic", "WordByteCodecs", "WordByteRoundtrip", "MemoryImage", "BytesWrite", "MemoryLayout", "MemoryStageGas",
          "Compiled", "DeploymentMessage", "DeploymentTouch", "Forward", "ForwardFlatAccess",
          "Reverts", "ForwardCall", "ForwardStorageAccess", "StorageAccessGas", "StorageRefund", "StorageRefundPotential", "ForwardSha256",
          "StaticPrecompileMessage", "StaticStorage", "TerminalStorage",
          "CompiledStackSafety", "AbstractStackSafety",
          "AbstractStackTransfer", "CodeTrie", "GasErasure", "RunPrefix", "PrefixTransport",
          "RevertPayload", "CompiledWalkInversion", "CompiledFixedInvariance", "ExecDeterminism", "ExecIdentification", "ExecutionSettlement", "ExecutionPath",
          "ExecutionStateTrace", "ExecutionTrace", "ExecutionStagedBodyTrace", "ExecutionStagedBodyStateTrace", "RequestsOutput", "ExecutionMessageStateTrace",
          "ExecutionTransactionStateTrace", "ExecutionSelectedTransactionStateTrace", "ExecutionTransactionGas", "ExecutionBodyGas", "ExecutionBodyStateTrace", "ExecutionHistory", "ExecutionBlockCommitments", "ExecutionHistoryExtension",
          "ExecutionHistoryStateTrace", "ExecutionHistoryInStateTrace", "ExecutionOccurrence", "ExecutionNoninterference", "TransientSettlement", "TransientInvariance", "ExecutionCreateGuard",
                                 "ExecutionDeletionProvenance",
                                 "ExecutionEmptyContext",
                                 "ExecutionNonceKeep",
                                 "ExecutionHistoryInAssociativity",
                                 "ExecutionHistoryInSystemEnvironment",
                                 "ExecutionHistoryInSystemOpenings",
                                 "ExecutionHistoryReceiptCensus",
                                 "ExecutionMidHistoryCallers",
                                 "ExecutionMidHistoryInCallerExclusion",
                                 "ExecutionNonceCode",
                                 "ExecutionRetainedCodeSettlement",
                                 "Lift.ConstructorTransaction",
                                 "Lift.CreateSettlementMeta",
                                 "Lift.SolcLibraryConstructor",
                                 "Lift.StaticOnlyFramesIn",
                                 "TransactionAdmissionProjection",
                                 "TransactionHistoricalForward"]
# Newly extracted common modules live in a separate additive row so concurrent
# contract branches can extend the historical table cleanly.
SHARED += ["MessageExecution", "MessageExecutionInversion",
           "LogBloom", "ExecutionBlockLogExclusion",
           "ExecutionSenderOccurrences", "ExecutionSenderRootCallers", "CodeReadInversion",
           "AddressSlot", "AddressSlotProofs", "MessageResult",
           "DelegatecallEnvelope",
           "ExecutionFrames", "ExecutionCommittedGas", "ExecutionMessageGas", "ExecutionFrameEntry", "ExecutionCallerExclusion", "ExecutionTraceCallerExclusion", "ExecutionFrameTime", "ExecutionHistoryFrameTime", "ExecutionAdmission", "ContractAdmission",
           "ExecutionMessageAdmission", "ExecutionTransactionAdmission",
           "ExecutionTransactionPrefix", "ExecutionTransactionPrefixAdmission",
           "ExecutionBodyAdmission", "ExecutionBodyPrefixAdmission", "ExecutionHistoryAdmission",
           "ExecutionTraceFresh", "ExecutionTraceEntered", "ExecutionImmutableCode",
           "ExecutionMessageEffects", "ExecutionTransactionEffects", "ExecutionTraceCreateResult", "ExecutionParentLogAttribution", "ExecutionSettledReceiptLogs",
           "ExecutionBodyEffects", "ExecutionRewardCredits", "ExecutionHistoryEffects",
           "ExecutionAccountingReplay", "ExecutionAccountingSignedBalance", "ExecutionAccountingStorageFold",
           "ExecutionAccountingStoragePrefix",
           "ExecutionAccountingLadder", "CallSpawnExact", "StaticcallObservation", "StaticCallStorage",
           "ChargeGas", "ExecutionTraceFrames", "ExecutionTraceAdmission", "ExecutionTraceSettledFrames", "ExecutionTraceSettledOrigin", "ExecutionTraceSettledFresh", "ExecutionStagedFrames", "ExecutionStagedAdmission", "ExecutionStagedFrameEnv", "ExecutionStagedRootFacts", "ExecutionStagedSstoreAttribution", "ExecutionTraceRootFrame", "ExecutionRequestSegments", "ExecutionTraceEntry", "ExecutionExistingAccount", "ExecutionDeletionSafety", "ExecutionRetainedDeletionSafety", "ExecutionNoDelProducer", "ExecutionNoDelSafeHistory", "ExecutionRetainedNoDelTransaction", "ExecutionRetainedNoDelHistory", "ExecutionTraceDeterminism", "ExecutionNoDelTransaction", "ExecutionNoDelHistory", "ExecutionHistoricalAdmission", "ExecutionHistoricalLadder",
           "ExecutionAccountingObserved", "ExecutionAccountingAdmission", "ExecutionAccountingCore", "ExecutionEntryAccounting", "ExecutionModelAccounting", "ExecutionWholeFrameAccounting", "ExecutionDirectCode", "ExecutionAccountingStepsIn", "ExecutionAccountingCoreIn", "ExecutionAccountingAdmissionIn", "ExecutionAccountingHistoryIn"]
# The ladder over arbitrary code images and the generic bytecode lift
# (solc-bytecode-v1): contract-neutral, no WETH9 name in any of them.
SHARED += ["LadderBase", "LadderReached", "MessageDelegationGas", "LadderSem", "ContractAdmissionSem", "ExecutionAdmissionSem",
           "Lift.Basic", "Lift.Check", "Lift.CallEffects", "Lift.Transfer", "Lift.Sound", "Lift.Exact",
           "Lift.ExactWalk", "Lift.Silent", "Lift.BalSilent"]
# Loops, kernel-economical checking, walk kits and solc idioms (beacon-deposit-bytecode-v1):
# contract-neutral, no contract name in any of them.
SHARED += ["Lift.Loop", "Lift.CheckFast", "Lift.CheckAssembly", "Lift.ExactWalkOps",
           "Lift.ExactWalkCut", "Lift.ExactWalkCutOps", "Lift.CopyLoop", "Lift.PackedSha",
           "Lift.PackedShaCovered", "Lift.Quiet", "Lift.InvWalk", "Lift.InvWalkOps",
           "Lift.InvWalkWorld", "Lift.InvWalkGas", "Lift.ExactMustRun", "Lift.InvWalkSha", "Lift.InvWalkDispatch", "Lift.InvWalkProvenance", "Lift.CodeSizeWalk", "Lift.HistAccessWalk", "Lift.HistStaticCall", "Lift.HistCursorCuts", "Lift.HistCursorReturn", "Lift.HistAccessFacts", "Lift.HistEcrecover", "Lift.HistCreate", "Lift.HistAccessMeta", "Lift.HistAccessWalkFacts"]
# Creation code (deploy-init-v1): the size-optimised packed-hash site and the CREATE bridge
# for lifted creation code; contract-neutral.
SHARED += ["RequestFeeWord", "Lift.RequestFee.Window", "Lift.RequestFee.Getter"]
SHARED += ["Lift.Deploy", "Lift.CreationOps", "Lift.Create2Deploy", "Lift.CreateEntry", "Lift.Clone1167", "Lift.CheckRange", "Lift.WitnessShadow"]
# Solc-0.4 scratch-memory walk kit and the value-bearing CALL to a code-free recipient
# (weth9-liveness-v1): contract-neutral.
SHARED += ["Lift.ExactWalkSolc", "Lift.ExactCallProfile", "Lift.CallProfileTransport", "Lift.StaticGasTransport", "Lift.StaticGasMessage"]
# Parameterized free-pointer memory for lifted walks.
SHARED += ["Lift.ExactWalkMemory", "Lift.WordImage", "Lift.Ecrecover", "Lift.EcrecoverCall", "Lift.SolcSignedQuery"]
# Free-pointer and write-site checker kits (usdc-neversigner-freepointer-v1):
# each imports only SHARED modules and Jaune, and no statement names a contract.
SHARED += ["Lift.MemPotential", "Lift.FreePtr", "Lift.SymTransfer", "Lift.FreePtrFacts",
           "Lift.WriteSite", "Lift.WriteSiteTerm", "Lift.WriteSiteObs", "Lift.WriteSiteLocality",
           "Lift.HistoryGas", "Lift.StepMemory", "Lift.FreePtrMem",
           "Lift.NodeRet", "Lift.FreePtrSoundStep", "Lift.FreePtrSound",
           "Lift.MemWrites", "Lift.StepTops", "Lift.WriteSiteStep", "Lift.WriteSiteJoin",
           "Lift.WriteSiteSound", "Lift.WriteSiteRows", "Lift.WriteSiteSelector", "Lift.WriteSiteZero",
           "Lift.WriteSiteReach", "Lift.WriteSiteReachHistory", "Lift.ReachWalkSstore"]
# The shared symbol-interval reading of the bound checkers (ns-h1b): imports
# nothing but core Lean, so it is contract-neutral.
SHARED += ["Lift.BndInterval", "Lift.ReturnDataKeep"]
# Chain assembly of `fpCert` from per-entry kernel decisions (ns-f5b): imports only
# Lift.FreePtr; no statement names a contract.
SHARED += ["Lift.FreePtrChain", "Lift.WriteSiteChain"]
# The root-message fold used by message-scenario headlines (V± capstones).
SHARED += ["Lift.RootMessages"]
# Size-free free-pointer word carrier for moved-pointer walks (uv2nh-skim)
SHARED += ["Lift.PtrWordMemory"]
# Retained target frames interleaved with actual foreign LOGs, and per-step storage/log
# transport across arbitrary callee code (uv2nh-skim2): contract-neutral.
SHARED += ["Lift.TargetLogEvents"]
# Forward construction of one configured block from proof-produced body evidence
# (eip7002-withdrawal-predeploy-v1): contract-neutral.
SHARED += ["BlockForward", "Lift.ExactWalkCallChild"]
# Pure-model ledger updates (vyper-3crv-bytecode-v1): contract-neutral.
SHARED += ["LedgerUpdate"]
# StableSwap (n = 3) Newton loops for D and y, plain and checked: contract-neutral.
SHARED += ["Lift.StableSwapNewton.Defs", "Lift.StableSwapNewton.Root",
           "Lift.StableSwapNewton.D", "Lift.StableSwapNewton.Y",
           "Lift.StableSwapNewton.Fuel"]
# Fuel-bounded loop heads (Newton loops) walked to a fuel-loop model: contract-neutral.
SHARED += ["Lift.FuelLoopWalk"]
# Vyper 0.2.x walk kit (array slots, identity copies, raw_call tails, balance differences):
# contract-neutral.
SHARED += ["Lift.VyperArraySlot", "Lift.IdentityCall", "Lift.BalanceDiffCall",
           "Lift.VyperRawCall", "Lift.RunEx", "Lift.WalkKit", "Lift.WalkInvKit", "Lift.FrameWalkAligned"]
# Internal calls through the PC idiom and unrolled Vyper frame save/restore chains: contract-neutral.
SHARED += ["Lift.InvWalkCallNext", "Lift.VyperFrameLoop"]
SHARED += ["Lift.ThreeWordFrame"]
# Vyper 0.2.x internal-callee walks: memory windows, load-only bases, checked arithmetic.
SHARED += ["Lift.VyperCallee", "Lift.VyperCheckedArith"]
# Token-ledger sums read over a finite covering key footprint: contract-neutral.
SHARED += ["Lift.LedgerFootprint"]
# Walking a successful frame's own derivation with its direct children: contract-neutral.
SHARED += ["Lift.FrameWalk"]
# Crossing certified exec-free callees from walked states, and memory glue: contract-neutral.
SHARED += ["Lift.SoundSpan", "Lift.FrameWalkNode", "Lift.FrameWalkCut", "Lift.MemGlue", "Lift.FrameWalkKit", "Lift.IdentityCallGas"]
# Ordinary interpreter output provenance for actual-call returndata bounds.
SHARED += ["Lift.ReturnDataBound", "Lift.PrecompileOutputBound"]
# Exact chunks and local simulation over existing configured state chronology.
SHARED += ["Lift.CommittedLogs", "Lift.CommittedFrameLogs", "Lift.SegmentedReplay", "Lift.SegmentedHistory"]
# Walk steps for arbitrary static calls, CALLER/KECCAK256/LOG3/SSTORE, hashed slots and the
# Vyper 0.2.x front end (vyper-3crv-bytecode-v1): contract-neutral.
SHARED += ["Lift.StaticCall", "Lift.StaticCallGuard", "Lift.WalkSteps", "Lift.MapSlot", "Lift.Vyper", "Lift.VyperDispatchWalk", "Lift.VyperDispatchExact", "Lift.PackedWord"]
# Spawn kinds from code bytes (curve-3pool-stableswap-v1): contract-neutral.
SHARED += ["Lift.SpawnKindsM"]
SHARED += ["Lift.GuardedCalls"]
SHARED += ["Lift.ChildFrameCode"]
SHARED += ["Lift.ChildFrameDepth"]
SHARED += ["Lift.LogAddresses"]
# The frame cursor, the reentrancy-lock exclusion kit and its bytecode checker, owner
# discipline, and concrete-run evaluation (deployed-lido-vyper-v1): contract-neutral.
SHARED += ["Lift.Reach", "Lift.ReachWalk", "Lift.ReachChain", "Lift.ReachDispatch", "Lift.Cursor", "Lift.CursorCuts", "Lift.CursorCheckPrefix", "Lift.ObservedReach", "Lift.ObservedReachSplit", "Lift.CursorKeccak", "Lift.CursorKeccakOrder", "Lift.CursorObservedCut", "Lift.CursorOccurrence", "Lift.CursorOccurrenceToward", "Lift.CursorCutsToward", "Lift.CursorStateToward", "Lift.CursorReturnToward", "Lift.CursorOccurrenceNoStateGas", "Lift.CursorTreeNinst", "Lift.CursorExact", "Lift.CursorExactLine", "Lift.CallRestriction", "Lift.StaticOnlyFrames", "Lift.StaticOnlyRoots", "LockExclusion", "OwnerDiscipline", "ConcreteRun",
           "Lift.LockCheck", "Lift.LockCheckSound", "Lift.LockCheckFlow", "Lift.CursorStateCuts", "Lift.CursorNoExecSuffix", "Lift.CursorSourceRun", "Lift.CursorSourceRunReturn", "Lift.CursorBalanceReply", "Lift.CursorQuietReturn", "Lift.CursorJump"]
# The constant memory map and its checker, code tries as data, and the executable-witness
# engine with its child runs and spawn facts (deployed-lido-vyper-v1, V-): contract-neutral.
SHARED += ["Lift.MemMap", "Lift.CheckMem", "Lift.CodeTriesData", "Lift.CodeTriesBuild", "Lift.WitnessArms", "Lift.Witness",
           "Lift.WitnessChild", "Lift.WitnessSpawn", "Lift.NodeWalk", "Lift.NodeWalkFrames", "Lift.KernelBatch", "Lift.KernelNat", "Lift.WitnessChildMeta"]
# Chunk boundaries and stage composition of a witness run, the literal-free scaffolding the
# V- witness's heavy frames instantiate (vminus-tx-v1): contract-neutral.
SHARED += ["Lift.WitnessBoundary", "TransactionForward", "TransactionForwardH"]
# The system-call envelope over a successful raw frame of canonical system code
# (eip7002-system-paths): contract-neutral.
SHARED += ["SystemCallForward"]
# Generic warmth / code-at-address / system-frame execution facts (beacon-env-v1): contract-neutral.
SHARED += ["ExecutionWarmth", "ExecutionErrorKeep", "ExecutionTraceWarmth", "ExecutionCodeAt", "ExecutionTraceCodeAt", "ExecutionTraceSystem"]
# Reachable program counters, the canonical consensus system-contract code and system frames that
# run it (beacon-env-v2): contract-neutral (the four system contracts are protocol, not a Blanc contract).
SHARED += ["ExecutionReachable", "SystemContracts", "ExecutionTraceCodeKeep", "ExecutionTraceSystemCode"]
# Call-only executions enter no CREATE frame (eip7002-withdrawal-predeploy-v1).
SHARED += ["ExecutionTraceCallOnly"]
# Generic per-frame calldata-length bound of a configured history (calldata-bound-v1): contract-neutral.
SHARED += ["ExecutionTraceCalldata", "ForkUniform", "Lift.NodeWalkFork", "Lift.WitnessFork", "TransactionFork", "Lift.NodeWalkPrecomp", "Lift.ShadowCanon", "Lift.NodeWalkOrig"]
# A gas-exact lifted run as a node-walk leaf child (vyper-reachable-reentrancy-v1).
SHARED += ["Lift.ExactLeaf"]
# A forall kernel batch (vyper-minus-reachable-reentrancy-v1).
SHARED += ["Lift.KernelBatchForall", "Lift.ShadowTail", "Lift.OrigKeys"]
# Generic entry-gas bound, child code-at keep and system-size exclusion of a configured history
# (curve-3pool-stableswap-v1 packet G): contract-neutral.
SHARED += ["ExecutionTraceFrameEnv"]

SHARED += ["Lift.GasErasureRun", "Lift.MutableCallPost", "Lift.WordWindowMemory"]


SHARED += ["Lift.CallChildren", "Lift.CallSite", "Lift.CallSiteChildren", "Lift.CallerProvenance"]
# Outermost settled frames at an address (committed-replay histories): contract-neutral.
SHARED += ["Lift.OutermostFrames"]

# The positional frame ladder, root-frame caller facts, the generic token core over a settled
# history, finite checkpoints, retained-target completeness and the EIP-7702 designator length
# fact (uniswap-weth9-composition-v1): contract-neutral.
SHARED += [
    "ExecutionAccountingPositional",
    "ExecutionAccountingPositionalHistory",
    "ExecutionTraceRootCallers",
    "Lift.FiniteCheckpoint",
    "Lift.RetainedTargetCompleteness",
    "Lift.Token.Abi",
    "Lift.Token.Core",
    "Lift.Token.Holder",
    "Lift.Token.SelfCaller",
    "CodeDelegation",
]
# The minter/supply facet of the token core (curve-3pool-stableswap-v1 U8a): contract-neutral.
SHARED += ["Lift.Token.Supply"]

# The settled-forest positional facts, own-code persistence at settled frames, certificate windows
# and the exact-word prefix stack transfer (uniswap-weth9-composition-v1, final integration):
# contract-neutral.
SHARED += [
    "ExecutionSettledOwnCode",
    "ExecutionTraceSettledForest",
]

# Owner closure and owner families, spawn/settled frame code images, the DELEGATECALL lift
# control, certificate chains and refinement, reach/skip/walk kits, the selector route, the
# word-keyed slot footprint and the CoreW token core with its signed and liveness extensions
# (usdc-weth9-pair-composition-v1): contract-neutral.
SHARED += [
    "ExecutionOwnerFamily",
    "ExecutionOwnerFamilyPositional",
    "ExecutionRawFramesCodeImage",
    "ExecutionSettledCodeImage",
    "ExecutionInCodeImage",
    "ExecutionInOwnCode",
    "ExecutionInCodeImageSafe",
    "ExecutionSafeRawFramesCodes",
    "ExecutionInRawNodes",
    "ExecutionCellProvenance",
    "ExecutionRetainedCellZero",
    "ExecutionRetainedCellAt",
    "ExecutionInCellProvenance",
    "ExecutionCommittedCell",
    "ExecutionSettledRootEntry",
    "ExecutionHistoryCommittedCell",
    "ExecutionHistoryInEraBounds",
    "ExecutionHistoryCommittedCuts",
    "ExecutionIndexedReceipts",
    "ExecutionTrieBinding",
    "ExecutionReceiptRanges",
    "ExecutionHistoryReceiptLogs",
    "ExecutionHistoryCellProvenance",
    "ExecutionInRawNodeOrigin",
    "ExecutionInRootOwnCode",
    "ExecutionRetainedNodeOrigin",
    "ExecutionHistoryCellProvenanceFrom",
    "ExecutionInRawNodeOriginFrom",
    "ExecutionSpawnFrames",
    "Lift.CertRefine",
    "Lift.CursorFrames",
    "Lift.DelegatecallControl",
    "Lift.FrameSkip",
    "Lift.InvWalkStep",
    "Lift.QuietDelegateSkip",
    "Lift.ReachFirstExec",
    "Lift.ReachPreExec",
    "Lift.ReachSilentTail",
    "Lift.ReachSkip",
    "Lift.RegionStor",
    "Lift.RunPWalk",
    "Lift.SolcStorageClear",
    "Lift.SolcStoragePayload",
    "Lift.SolcStringAllocation",
    "Lift.SolcAbiStringStaging",
    "Lift.SolcStorageReturn",
    "Lift.ReachSstoreLoops",
    "Lift.ReachSolcStringStore",
    "Lift.SelectorRoute", "Lift.SettledFramePositions", "Lift.ShuffleSkip",
    "Lift.SpawnExact",
    "Lift.HistSpawnExact",
    "Lift.StaticOnlyPrefix",
    "Lift.Token.CoreW",
    "Lift.Token.FamilyReplay",
    "Lift.Token.HolderLaws",
    "Lift.Token.Signed",
    "Lift.Token.SignedControl",
    "Lift.Token.TransferLiveBudget",
    "Lift.WalkCutKit",
    "OwnerClosure",
    "OwnerClosureControl",
    "SlotFootprintWord",
]

# Concatenation of selected-domain In-histories with the modern-to-historical
# bridge (beacon-deposit-historical-reach-v1): contract-neutral.
SHARED += [
    "ExecutionHistoryInAppend",
]

# Selected-domain In-histories that start in the middle of a block, and their
# accounting replay rungs (beacon-deposit-historical-reach-v1, W3): contract-neutral.
SHARED += [
    "ExecutionMidHistoryIn",
    "ExecutionInstalledCertCuts",
    "ExecutionAccountingMidHistoryIn",
]

# Block-local facts transported to mid-block In-histories (reward funding, entered
# conditions, root entry, calldata bound) (weth9-pair-historical-extension-v1): contract-neutral.
SHARED += [
    "ExecutionMidHistoryInFacts",
    "ExecutionMidHistoryInForest",
    "ExecutionMidHistoryInNoDel",
]

# Fork-era schedule facts and historical environment facts for selected-domain
# In-histories (beacon-deposit-historical-reach-v1): contract-neutral.
SHARED += [
    "ExecutionHistoryInForkFacts",
    "ExecutionHistoryInSystemCodeKeep",
    "ExecutionHistoryInWarmth",
    "ExecutionHistoryInCodeAt",
    "ExecutionHistoryInSystemFrames",
    "ExecutionHistoryInCreateAvoid",
]

# Concrete canonical system-operation proof support for featured configured histories.
# These modules implement required system calls; they are not standalone exhibits.
SHARED += ['Lift.SystemExecution.BeaconRoots.Cert', 'Lift.SystemExecution.BeaconRoots.Check', 'Lift.SystemExecution.BeaconRoots.Jumps', 'Lift.SystemExecution.BeaconRoots.Prog', 'Lift.SystemExecution.BeaconRoots.SystemWalk', 'Lift.SystemExecution.HistoryStorage.Cert', 'Lift.SystemExecution.HistoryStorage.Check', 'Lift.SystemExecution.HistoryStorage.Jumps', 'Lift.SystemExecution.HistoryStorage.Prog', 'Lift.SystemExecution.HistoryStorage.SystemWalk', 'Lift.SystemExecution.ConsolidationRequest.Cert', 'Lift.SystemExecution.ConsolidationRequest.Check', 'Lift.SystemExecution.ConsolidationRequest.Jumps', 'Lift.SystemExecution.ConsolidationRequest.Prog', 'Lift.SystemExecution.ConsolidationRequest.SystemWalk']

CONTRACTS = {
    "withdrawal-request": ["Lift.WithdrawalRequest.AmsterdamSystem", "Lift.WithdrawalRequest.Cert", "Lift.WithdrawalRequest.Check",
                           "Lift.WithdrawalRequest.Jumps", "Lift.WithdrawalRequest.Model",
                           "Lift.WithdrawalRequest.Layout", "Lift.WithdrawalRequest.Prog",
                           "Lift.WithdrawalRequest.Dispatch", "Lift.WithdrawalRequest.SystemSetup",
                           "Lift.WithdrawalRequest.UserSetup", "Lift.WithdrawalRequest.FeeLoop",
                           "Lift.WithdrawalRequest.SystemMemory", "Lift.WithdrawalRequest.SystemAmount",
                           "Lift.WithdrawalRequest.SystemBody", "Lift.WithdrawalRequest.UserFeeDispatch",
                           "Lift.WithdrawalRequest.FeeGetter", "Lift.WithdrawalRequest.SystemLoop",
                           "Lift.WithdrawalRequest.SystemImage", "Lift.WithdrawalRequest.SystemOutput",
                           "Lift.WithdrawalRequest.SubmissionState", "Lift.WithdrawalRequest.SubmissionBody",
                           "Lift.WithdrawalRequest.SystemBookkeepingState",
                           "Lift.WithdrawalRequest.SystemBookkeeping",
                           "Lift.WithdrawalRequest.SystemStorage", "Lift.WithdrawalRequest.SubmissionLayout",
                           "Lift.WithdrawalRequest.SystemMemoryGas", "Lift.WithdrawalRequest.SystemGas",
                           "Lift.WithdrawalRequest.FrameEffects",
                           "Lift.WithdrawalRequest.BalanceHistory", "Lift.WithdrawalRequest.BlockRequests",
                           "Lift.WithdrawalRequest.WordReplay", "Lift.WithdrawalRequest.NatFee",
                           "Lift.WithdrawalRequest.WordBudget",
                           "Lift.WithdrawalRequest.NatFeeBound",
                           "Lift.WithdrawalRequest.NumericFacts",
                           "Lift.WithdrawalRequest.WordModelReplay",
                           "Lift.WithdrawalRequest.WordModelCount",
                           "Lift.WithdrawalRequest.UserOccurrence",
                           "Lift.WithdrawalRequest.ProtocolOccurrences",
                           "Lift.WithdrawalRequest.ModelBlockRequests",
                           "Lift.WithdrawalRequest.WordHistory",
                           "Lift.WithdrawalRequest.WordFifo", "Lift.WithdrawalRequest.WordDelivery",
                           "Lift.WithdrawalRequest.HistoryFifo",
                           "Lift.WithdrawalRequest.InhibitedHistory",
                           "Lift.WithdrawalRequest.InhibitedObservations",
                           "Lift.WithdrawalRequest.DeploymentHistory",
                           "Lift.WithdrawalRequest.ResetOccurrence",
                           "Lift.WithdrawalRequest.ExactFeeDomain",
                           "Lift.WithdrawalRequest.NatLiveness",
                           "Lift.WithdrawalRequest.SubmissionCount",
                           "Lift.WithdrawalRequest.ResetWindowCount",
                           "Lift.WithdrawalRequest.CodeFacts",
                           "Lift.WithdrawalRequest.Semantics",
                           "Lift.WithdrawalRequest.SystemHistory",
                           "Lift.WithdrawalRequest.SystemProtocol",
                           "Lift.WithdrawalRequest.UserGas",
                           "Lift.FloodLooper.Cert", "Lift.FloodLooper.Check",
                           "Lift.FloodLooper.Jumps",
                           "Lift.WithdrawalRequest.FloodWalk", "Lift.WithdrawalRequest.FloodRun",
                           "Lift.WithdrawalRequest.FloodTx",
                           "Lift.WithdrawalRequest.FloodTxRecover",
                           "Lift.WithdrawalRequest.SystemDrain",
                           "Lift.WithdrawalRequest.SystemFrameEffects",
                           "Lift.WithdrawalRequest.DrainTx",
                           "Lift.WithdrawalRequest.FifoDrainControl",
                           "Lift.SystemDrainer.Cert", "Lift.SystemDrainer.Check",
                           "Lift.SystemDrainer.Jumps",
                           "Lift.WithdrawalRequest.Creation.Address",
                           "Lift.WithdrawalRequest.Creation.Block",
                           "Lift.WithdrawalRequest.Creation.Transaction",
                           "Lift.WithdrawalRequest.Creation.Cert",
                           "Lift.WithdrawalRequest.Creation.Check",
                           "Lift.WithdrawalRequest.Creation.Deploy",
                           "Lift.WithdrawalRequest.Creation.Init",
                           "Lift.WithdrawalRequest.Creation.Input",
                           "Lift.WithdrawalRequest.Creation.State",
                           "Lift.WithdrawalRequest.Creation.Walk",
                           "Lift.WithdrawalRequest.Creation.HistoricalTxRaw",
                           "Lift.WithdrawalRequest.Creation.HistoricalTxRecover",
                           "Lift.WithdrawalRequest.Creation.HistoricalTxTrace",
                           "Lift.WithdrawalRequest.MainnetDeployment",
                           "Lift.WithdrawalRequest.HeadlineFee",
                           "Lift.WithdrawalRequest.HeadlineSystem",
                           "Lift.WithdrawalRequest.HeadlineHistory"],
    # The 3Crv LP token (CurveTokenV2.vy, Vyper 0.2.4): the model from source and the deployed runtime,
    # lifted (vyper-3crv-bytecode-v1).
    "curve-3crv": ["Curve3Crv.Model", "Curve3Crv.Properties", "Lift.Curve3Crv.Cert", "Lift.Curve3Crv.Check", "Lift.Curve3Crv.Creation.Cert", "Lift.Curve3Crv.Creation.Check", "Lift.Curve3Crv.Creation.Deploy", "Lift.Curve3Crv.Creation.HistoricalDeploy", "Lift.Curve3Crv.Creation.HistoricalTx", "Lift.Curve3Crv.Creation.HistoricalTxRaw", "Lift.Curve3Crv.Creation.HistoricalTxRecover", "Lift.Curve3Crv.Creation.HistoricalTxInput", "Lift.Curve3Crv.Creation.HistoricalTxSettle", "Lift.Curve3Crv.Creation.HistoricalTxTrace", "Lift.Curve3Crv.Creation.HistoricalWalk", "Lift.Curve3Crv.Creation.Walk", "Lift.Curve3Crv.Jumps",
                   "Lift.Curve3Crv.Lift", "Lift.Curve3Crv.Prog", "Lift.Curve3Crv.Layout",
                   "Lift.Curve3Crv.Decode", "Lift.Curve3Crv.Spec", "Lift.Curve3Crv.ViewBodies",
                   "Lift.Curve3Crv.Dispatch", "Lift.Curve3Crv.Refine", "Lift.Curve3Crv.SafeBodies",
                   "Lift.Curve3Crv.SafeViewBodies", "Lift.Curve3Crv.SafeViews", "Lift.Curve3Crv.LiveBodies", "Lift.Curve3Crv.Safe",
                   "Lift.Curve3Crv.Exec", "Lift.Curve3Crv.Slots", "Lift.Curve3Crv.Ladder",
                   "Lift.Curve3Crv.HistoryKeys", "Lift.Curve3Crv.CarriedHistory",
                   "Lift.Curve3Crv.CommittedReplay", "Lift.Curve3Crv.CommittedExec",
                   "Lift.Curve3Crv.CommittedHistory", "Lift.Curve3Crv.HistCommittedHistory", "Lift.Curve3Crv.HistDeployment", "Lift.Curve3Crv.FrameReplay", "Lift.Curve3Crv.Headline",
                   "Lift.Curve3Crv.Init", "Lift.Curve3Crv.Liveness",
                   "Lift.Curve3Crv.CostBounds"],
    # The Curve 3pool StableSwap (StableSwap3Pool.vy, Vyper 0.2.4): the deployed creation input,
    # lifted runtime and creation input, its functional model, U5, the U3 refutation and bounds, the storage
    # abstraction and checkpoint predicate, U7 deployment, and the U2 pure refinement layer (curve-3pool-stableswap-v1).
    "curve-3pool": ["Lift.Curve3Pool.Creation.Cert",
                    "Lift.Curve3Pool.Creation.Check",
                    "Lift.Curve3Pool.Creation.Jumps",
                    "Lift.Curve3Pool.Model",
                    "Lift.Curve3Pool.SpawnKinds",
                    "Lift.Curve3Pool.CallGuards",
                    "Lift.Curve3Pool.Bridge",
                    "Lift.Curve3Pool.U5",
                    "Lift.Curve3Pool.U3Refute",
                    "Lift.Curve3Pool.U4ExactnessRefute",
                    "Lift.Curve3Pool.U4GetYRefute",
                    "Lift.Curve3Pool.U3Observable",
                    "Lift.Curve3Pool.U3Bounds",
                    "Lift.Curve3Pool.Layout",
                    "Lift.Curve3Pool.Creation.Walk",
                    "Lift.Curve3Pool.Creation.Deploy",
                    "Lift.Curve3Pool.Decode",
                    "Lift.Curve3Pool.Observe",
                    "Lift.Curve3Pool.FrameEnv",
                    "Lift.Curve3Pool.Spec",
                    "Lift.Curve3Pool.Refine",
                    "Lift.Curve3Pool.Walk.Quiet",
                    "Lift.Curve3Pool.Walk.Admin",
                    "Lift.Curve3Pool.Walk.AdminBalances",
                    "Lift.Curve3Pool.Walk.Donate",
                    "Lift.Curve3Pool.Walk.Getters",
                    "Lift.Curve3Pool.Cert",
                    "Lift.Curve3Pool.Code",
                    "Lift.Curve3Pool.KitCheck",
                    "Lift.Curve3Pool.Callee.A",
                    "Lift.Curve3Pool.Callee.ABase",
                    "Lift.Curve3Pool.Callee.Xp", "Lift.Curve3Pool.Callee.GetD", "Lift.Curve3Pool.Callee.GetDExact", "Lift.Curve3Pool.Callee.GetDLoop", "Lift.Curve3Pool.Callee.GetDMem", "Lift.Curve3Pool.Callee.GetDMemExact", "Lift.Curve3Pool.Callee.GetY", "Lift.Curve3Pool.Callee.GetYCoins", "Lift.Curve3Pool.Callee.GetYExact", "Lift.Curve3Pool.Callee.GetYLoop", "Lift.Curve3Pool.Callee.GetYTrees", "Lift.Curve3Pool.Callee.GetDTrees", "Lift.Curve3Pool.Callee.GetYD", "Lift.Curve3Pool.Callee.GetYDCoins", "Lift.Curve3Pool.Callee.GetYDExact", "Lift.Curve3Pool.Callee.GetYDLoop", "Lift.Curve3Pool.Callee.GetYDTrees",
                    "Lift.Curve3Pool.CheckTries",
                    "Lift.Curve3Pool.Check",
                    "Lift.Curve3Pool.CheckPart0",
                    "Lift.Curve3Pool.CheckPart1",
                    "Lift.Curve3Pool.CheckPart2",
                    "Lift.Curve3Pool.CheckPart3",
                    "Lift.Curve3Pool.CheckPart4",
                    "Lift.Curve3Pool.CheckPart5",
                    "Lift.Curve3Pool.CheckPart6",
                    "Lift.Curve3Pool.CheckPart7",
                    "Lift.Curve3Pool.CheckPart8",
                    "Lift.Curve3Pool.CheckPart9",
                    "Lift.Curve3Pool.CheckPart10",
                    "Lift.Curve3Pool.CheckPart11",
                    "Lift.Curve3Pool.CheckPart12",
                    "Lift.Curve3Pool.CheckPart13",
                    "Lift.Curve3Pool.CheckPart14",
                    "Lift.Curve3Pool.CheckPart15",
                    "Lift.Curve3Pool.CheckPart16",
                    "Lift.Curve3Pool.CheckPart17",
                    "Lift.Curve3Pool.CheckPart18",
                    "Lift.Curve3Pool.CheckPart19",
                    "Lift.Curve3Pool.CheckPart20",
                    "Lift.Curve3Pool.CheckPart21",
                    "Lift.Curve3Pool.CheckPart22",
                    "Lift.Curve3Pool.CheckPart23",
                    "Lift.Curve3Pool.Creation.Input",
                    "Lift.Curve3Pool.Creation.Window",
                    "Lift.Curve3Pool.Walk.Kit", "Lift.Curve3Pool.Walk.AutoStep",
                    "Lift.Curve3Pool.Walk.Dispatch", "Lift.Curve3Pool.Walk.DispatchLive",
                    "Lift.Curve3Pool.Walk.RemoveLiquidityPre",
                    "Lift.Curve3Pool.Walk.RemoveLiquidityLoop",
                    "Lift.Curve3Pool.Walk.RemoveLiquidityPost",
                    "Lift.Curve3Pool.Walk.RemoveLiquidity",
                    "Lift.Curve3Pool.Walk.RemoveLiquiditySafe",
                    "Lift.Curve3Pool.Walk.RemoveLiquidityRawK",
                    "Lift.Curve3Pool.Walk.AdminBalancesX",
                    "Lift.Curve3Pool.Walk.DonateX",
                    "Lift.Curve3Pool.Walk.WithdrawAdminFeesX",
                    "Lift.Curve3Pool.Walk.WithdrawAdminFeesRaw",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceModel",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceChecks",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceDispatch",
                    "Lift.Curve3Pool.Walk.LiveKit",
                    "Lift.Curve3Pool.LivePremises",
                    "Lift.Curve3Pool.ExactLivePremises",
                    "Lift.Curve3Pool.CalldataWords",
                    "Lift.Curve3Pool.Walk.RemoveLiquidityLive",
                    "Lift.Curve3Pool.RemoveLiquidityLiveness",
                    "Lift.Curve3Pool.Walk.RemoveLiquidityExactSchedule",
                    "Lift.Curve3Pool.Walk.RemoveLiquidityExactWalk",
                    "Lift.Curve3Pool.RemoveLiquidityExactFrame", "Lift.Curve3Pool.Walk.ArmChecks", "Lift.Curve3Pool.Walk.Fallback", "Lift.Curve3Pool.Walk.AdminRaw",
                    "Lift.Curve3Pool.Walk.ExchangeDispatch",
                    "Lift.Curve3Pool.Walk.ExchangeFrame",
                    "Lift.Curve3Pool.Walk.ExchangePre",
                    "Lift.Curve3Pool.Walk.ExchangeChecks",
                    "Lift.Curve3Pool.Walk.ExchangeMid",
                    "Lift.Curve3Pool.Walk.ExchangePull",
                    "Lift.Curve3Pool.Walk.ExchangeTail",
                    "Lift.Curve3Pool.Walk.ExchangeX",
                    "Lift.Curve3Pool.Walk.ExchangeY",
                    "Lift.Curve3Pool.Walk.ExchangeDy",
                    "Lift.Curve3Pool.Walk.ExchangePush",
                    "Lift.Curve3Pool.Walk.ExchangeFront",
                    "Lift.Curve3Pool.Walk.Exchange",
                    "Lift.Curve3Pool.Walk.ExchangeModel",
                    "Lift.Curve3Pool.Walk.ExchangeObserve",
                    "Lift.Curve3Pool.Walk.ExchangeSafe",
                    "Lift.Curve3Pool.Walk.ExchangeLiveKit",
                    "Lift.Curve3Pool.Walk.ExchangeLiveFront",
                    "Lift.Curve3Pool.Walk.ExchangeLivePre",
                    "Lift.Curve3Pool.Walk.ExchangeLiveMid",
                    "Lift.Curve3Pool.Walk.ExchangeLivePull",
                    "Lift.Curve3Pool.Walk.ExchangeLiveBal",
                    "Lift.Curve3Pool.Walk.ExchangeLiveX",
                    "Lift.Curve3Pool.Walk.ExchangeLiveSave",
                    "Lift.Curve3Pool.Walk.ExchangeLiveRestore",
                    "Lift.Curve3Pool.Walk.ExchangeLiveY",
                    "Lift.Curve3Pool.Walk.ExchangeLiveDy",
                    "Lift.Curve3Pool.Walk.ExchangeLiveStore",
                    "Lift.Curve3Pool.Walk.ExchangeLivePush",
                    "Lift.Curve3Pool.Walk.ExchangeLiveFrame",
                    "Lift.Curve3Pool.Walk.ExchangeLiveModel",
                    "Lift.Curve3Pool.Walk.ExchangeLiveWords",
                    "Lift.Curve3Pool.ExchangeLive",
                    "Lift.Curve3Pool.ExchangeExactSchedule",
                    "Lift.Curve3Pool.Walk.ExchangeExactWalk",
                    "Lift.Curve3Pool.ExchangeExactLive",
                    "Lift.Curve3Pool.Walk.LiveLoops",
                    "Lift.Curve3Pool.Callee.AGrow",
                    "Lift.Curve3Pool.Callee.CalcWithdrawLiveA",
                    "Lift.Curve3Pool.Callee.CalcWithdrawLiveB",
                    "Lift.Curve3Pool.Callee.CalcWithdrawLiveC",
                    "Lift.Curve3Pool.Callee.CalcWithdrawLiveD",
                    "Lift.Curve3Pool.Callee.CalcWithdrawLiveLoop",
                    "Lift.Curve3Pool.Callee.CalcWithdrawLiveE",
                    "Lift.Curve3Pool.Callee.CalcWithdrawLive",
                    "Lift.Curve3Pool.Walk.OneCoinLiveP1",
                    "Lift.Curve3Pool.Walk.OneCoinLiveP2",
                    "Lift.Curve3Pool.Walk.OneCoinLiveFront",
                    "Lift.Curve3Pool.Walk.OneCoinLiveFrame",
                    "Lift.Curve3Pool.Walk.OneCoinLiveModel",
                    "Lift.Curve3Pool.Walk.OneCoinLiveWords",
                    "Lift.Curve3Pool.OneCoinLive",
                    "Lift.Curve3Pool.Walk.OneCoinExactSchedule",
                    "Lift.Curve3Pool.Walk.OneCoinExactWalk",
                    "Lift.Curve3Pool.OneCoinExactFrame",
                    "Lift.Curve3Pool.Callee.GetDMemGrow",
                    "Lift.Curve3Pool.Walk.RliLiveFront",
                    "Lift.Curve3Pool.Walk.RliLiveD",
                    "Lift.Curve3Pool.Walk.RliLiveD1",
                    "Lift.Curve3Pool.Walk.RliLiveFee",
                    "Lift.Curve3Pool.Walk.RliLiveD2",
                    "Lift.Curve3Pool.Walk.RliLivePush",
                    "Lift.Curve3Pool.Walk.RliLiveEnd",
                    "Lift.Curve3Pool.Walk.RliLiveTail",
                    "Lift.Curve3Pool.Walk.RliLiveFrame",
                    "Lift.Curve3Pool.Walk.RliLiveModel",
                    "Lift.Curve3Pool.Walk.RliLiveWords",
                    "Lift.Curve3Pool.Walk.LiveLink",
                    "Lift.Curve3Pool.Walk.RliLiveCut",
                    "Lift.Curve3Pool.RemoveImbalanceLive",
                    "Lift.Curve3Pool.AddLiquidityLive",
                    "Lift.Curve3Pool.Walk.AlLiveFront",
                    "Lift.Curve3Pool.Walk.AlLiveD0",
                    "Lift.Curve3Pool.Walk.AlLiveHead",
                    "Lift.Curve3Pool.Walk.AlLiveCredit",
                    "Lift.Curve3Pool.Walk.AlLivePull",
                    "Lift.Curve3Pool.Walk.AlLiveBal",
                    "Lift.Curve3Pool.Walk.AlLiveLoop",
                    "Lift.Curve3Pool.Walk.AlLiveD1",
                    "Lift.Curve3Pool.Walk.AlLiveFee",
                    "Lift.Curve3Pool.Walk.AlLiveD2",
                    "Lift.Curve3Pool.Walk.AlLiveD2Get",
                    "Lift.Curve3Pool.Walk.AlLiveMint",
                    "Lift.Curve3Pool.Walk.AlLiveBack",
                    "Lift.Curve3Pool.Walk.AlLiveMid",
                    "Lift.Curve3Pool.Walk.AlLiveFrame",
                    "Lift.Curve3Pool.Walk.AlLiveCut",
                    "Lift.Curve3Pool.Walk.AlLiveModel",
                    "Lift.Curve3Pool.Walk.AlLiveWords",
                    "Lift.Curve3Pool.Walk.AlLiveUnique",
                    "Lift.Curve3Pool.Walk.AlLiveLink",
                    "Lift.Curve3Pool.Walk.AddLiquidityExactKit",
                    "Lift.Curve3Pool.Walk.AddLiquidityExactSchedule",
                    "Lift.Curve3Pool.Walk.AddLiquidityExactLoop",
                    "Lift.Curve3Pool.Walk.AddLiquidityExactLoopRun",
                    "Lift.Curve3Pool.Walk.AddLiquidityExactFee",
                    "Lift.Curve3Pool.Walk.AddLiquidityExactBack",
                    "Lift.Curve3Pool.Walk.AddLiquidityExactWalk",
                    "Lift.Curve3Pool.AddLiquidityExactFrame",
                    "Lift.Curve3Pool.Walk.RliExactKit",
                    "Lift.Curve3Pool.Walk.RliExactSchedule",
                    "Lift.Curve3Pool.Walk.RliExactWalk",
                    "Lift.Curve3Pool.RemoveLiquidityImbalanceExactFrame",
                    "Lift.Curve3Pool.Walk.ViewsDispatch",
                    "Lift.Curve3Pool.Walk.ViewsLoop",
                    "Lift.Curve3Pool.Walk.ViewsKit",
                    "Lift.Curve3Pool.Walk.ViewsGvp",
                    "Lift.Curve3Pool.Walk.ViewsGvpRaw",
                    "Lift.Curve3Pool.Walk.ViewsA",
                    "Lift.Curve3Pool.Walk.BridgeChecks",
                    "Lift.Curve3Pool.Walk.RampKit",
                    "Lift.Curve3Pool.Walk.RampStop",
                    "Lift.Curve3Pool.Walk.RampA",
                    "Lift.Curve3Pool.Walk.ViewsDy",
                    "Lift.Curve3Pool.Walk.ViewsDyKit",
                    "Lift.Curve3Pool.Walk.ViewsDyPost",
                    "Lift.Curve3Pool.Walk.ViewsDyRaw",
                    "Lift.Curve3Pool.Walk.ViewsDyu",
                    "Lift.Curve3Pool.Walk.ViewsDyuPost",
                    "Lift.Curve3Pool.Walk.ViewsDyuRaw",
                    "Lift.Curve3Pool.Walk.ViewsCta",
                    "Lift.Curve3Pool.Walk.ViewsCtaLoop",
                    "Lift.Curve3Pool.Walk.ViewsCtaD1",
                    "Lift.Curve3Pool.Walk.ViewsCtaPost",
                    "Lift.Curve3Pool.Walk.ViewsCtaRaw",
                    "Lift.Curve3Pool.Walk.ViewsCwo",
                    "Lift.Curve3Pool.Walk.OneCoinPre",
                    "Lift.Curve3Pool.Walk.OneCoinBurn",
                    "Lift.Curve3Pool.Walk.OneCoinCalls",
                    "Lift.Curve3Pool.Walk.OneCoin",
                    "Lift.Curve3Pool.Walk.OneCoinRaw",
                    "Lift.Curve3Pool.Walk.OneCoinChecks",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceFront",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceD0",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceD1",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceFeeLoop",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceD2",
                    "Lift.Curve3Pool.Walk.RemoveImbalancePush",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceBurn",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceTransfers",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceWalk",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceRaw",
                    "Lift.Curve3Pool.Walk.RemoveImbalanceRawChecks",
                    "Lift.Curve3Pool.Callee.CalcWithdrawX",
                    "Lift.Curve3Pool.Callee.CalcWithdrawXB",
                    "Lift.Curve3Pool.Callee.CalcWithdrawXC",
                    "Lift.Curve3Pool.Callee.CalcWithdrawXLoop",
                    "Lift.Curve3Pool.Callee.CalcWithdrawXD",
                    "Lift.Curve3Pool.Callee.CalcWithdrawXSpec",
                    "Lift.Curve3Pool.Callee.CalcWithdrawXFirst",
                    "Lift.Curve3Pool.CommittedReplay",
                    "Lift.Curve3Pool.Ladder",
                    "Lift.Curve3Pool.Safe",
                    "Lift.Curve3Pool.History",
                    "Lift.Curve3Pool.AmpHistory",
                    "Lift.Curve3Pool.U3History",
                    "Lift.Curve3Pool.HistoryLive",
                    "Lift.Curve3Pool.ExactStaticGas",
                    "Lift.Curve3Pool.ExactMessage",
                    "Lift.Curve3Pool.HistoryLiveExact",
                    "Lift.Curve3Pool.SupplyMoves",
                    "Lift.Curve3Pool.U3Ledger",
                    "Lift.Curve3Pool.U4Frames",
                    "Lift.Curve3Pool.Walk.AddLiquidityKit",
                    "Lift.Curve3Pool.Walk.AddLiquidityFrames",
                    "Lift.Curve3Pool.Walk.AddLiquidityPre",
                    "Lift.Curve3Pool.Walk.AddLiquidityD0",
                    "Lift.Curve3Pool.Walk.AddLiquidityPull",
                    "Lift.Curve3Pool.Walk.AddLiquidityPull2",
                    "Lift.Curve3Pool.Walk.AddLiquidityIter",
                    "Lift.Curve3Pool.Walk.AddLiquidityD1",
                    "Lift.Curve3Pool.Walk.AddLiquidityFee",
                    "Lift.Curve3Pool.Walk.AddLiquidityFeeLoop",
                    "Lift.Curve3Pool.Walk.AddLiquidityD2",
                    "Lift.Curve3Pool.Walk.AddLiquidityMint",
                    "Lift.Curve3Pool.Walk.AddLiquidityTail",
                    "Lift.Curve3Pool.Walk.AddLiquidity",
                    "Lift.Curve3Pool.Walk.AddLiquidityBack",
                    "Lift.Curve3Pool.Walk.AddLiquiditySafe",
                    "Lift.Curve3Pool.Walk.AddLiquidityChecks"],
    # The deployed Vyper 0.3.7 nonreentrant comparator 0x847e and its proxy (deployed-lido-vyper-v1).
    "vyper-nonreentrant-deployed": ["Lift.VyperNonreentrantDeployed.Code", "Lift.VyperNonreentrantDeployed.CodeFacts", "Lift.VyperNonreentrantDeployed.Concrete.Fixture", "Lift.VyperNonreentrantDeployed.Concrete.ProxyConcrete", "Lift.VyperNonreentrantDeployed.Fixed.Cert", "Lift.VyperNonreentrantDeployed.Fixed.Check", "Lift.VyperNonreentrantDeployed.Fixed.Exclusion", "Lift.VyperNonreentrantDeployed.Fixed.ExclusionTrace", "Lift.VyperNonreentrantDeployed.Fixed.LockAnn", "Lift.VyperNonreentrantDeployed.Fixed.LockCheck", "Lift.VyperNonreentrantDeployed.Fixed.LockDominance", "Lift.VyperNonreentrantDeployed.Fixed.LockSpec", "Lift.VyperNonreentrantDeployed.ProxyEntry", "Lift.VyperNonreentrantDeployed.Fixed.CheckPart0", "Lift.VyperNonreentrantDeployed.Fixed.CheckPart1", "Lift.VyperNonreentrantDeployed.Fixed.CheckPart2", "Lift.VyperNonreentrantDeployed.Fixed.CheckPart3", "Lift.VyperNonreentrantDeployed.Fixed.CheckTries", "Lift.VyperNonreentrantDeployed.Fixed.Reader.Cert", "Lift.VyperNonreentrantDeployed.Fixed.Witness.Setup", "Lift.VyperNonreentrantDeployed.Fixed.Witness.RunF", "Lift.VyperNonreentrantDeployed.Fixed.Witness.RunRest", "Lift.VyperNonreentrantDeployed.Fixed.Witness.Top", "Lift.VyperNonreentrantDeployed.Vulnerable.Attacker.Cert", "Lift.VyperNonreentrantDeployed.Vulnerable.Cert", "Lift.VyperNonreentrantDeployed.Vulnerable.Check", "Lift.VyperNonreentrantDeployed.Vulnerable.CheckPart0", "Lift.VyperNonreentrantDeployed.Vulnerable.CheckPart1", "Lift.VyperNonreentrantDeployed.Vulnerable.CheckPart2", "Lift.VyperNonreentrantDeployed.Vulnerable.CheckPart3", "Lift.VyperNonreentrantDeployed.Vulnerable.CheckPart4", "Lift.VyperNonreentrantDeployed.Vulnerable.CheckPart5", "Lift.VyperNonreentrantDeployed.Vulnerable.CheckTries", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame0", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame1", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Full", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Kernel", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame1Run", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame2", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame3", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame4", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Child", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame4ChunkA", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame4ChunkB", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Chunks", "Lift.VyperNonreentrantDeployed.Vulnerable.Frame4Full", "Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC", "Lift.VyperNonreentrantDeployed.Vulnerable.TxCRecover", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Run", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Entry", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Outer", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.OuterAt", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Fork", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.ForkKernel", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame1", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame2Full", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame2Kernel", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame2Run", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame3", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame4", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5Child", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5ChunkA", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5ChunkB", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5Chunks", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5Full", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Closed", "Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Envelope", "Lift.VyperNonreentrantDeployed.Vulnerable.ForkFrames", "Lift.VyperNonreentrantDeployed.Vulnerable.ForkKernel", "Lift.VyperNonreentrantDeployed.Vulnerable.ForkTop", "Lift.VyperNonreentrantDeployed.Vulnerable.Locks", "Lift.VyperNonreentrantDeployed.Vulnerable.SubtreeRun", "Lift.VyperNonreentrantDeployed.Vulnerable.Token.Cert", "Lift.VyperNonreentrantDeployed.Vulnerable.Top", "Lift.VyperNonreentrantDeployed.Vulnerable.WitnessCerts", "Lift.VyperNonreentrantDeployed.Vulnerable.Attacker2.Cert", "Lift.VyperNonreentrantDeployed.Vulnerable.Attacker2.Check", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Outer", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Closed", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Envelope", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame1", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame2Full", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame2Kernel", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame2Run", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame3", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame4", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5Child", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5Full", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5ChunkB", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5ChunkA", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5Chunks", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame5", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Entry", "Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Run", "Lift.VyperNonreentrantDeployed.Vulnerable.TxTop", "Lift.VyperNonreentrantDeployed.Fixed.Receiver.Cert", "Lift.VyperNonreentrantDeployed.Fixed.Witness2.Setup", "Lift.VyperNonreentrantDeployed.Fixed.Witness2.Run", "Lift.VyperNonreentrantDeployed.Fixed.Witness2.Frames", "Lift.VyperNonreentrantDeployed.Fixed.Witness2.Top", "Lift.VyperNonreentrantDeployed.Fixed.Creation.Input", "Lift.VyperNonreentrantDeployed.Fixed.Creation.Cert", "Lift.VyperNonreentrantDeployed.Fixed.Creation.Check", "Lift.VyperNonreentrantDeployed.Fixed.Creation.State", "Lift.VyperNonreentrantDeployed.Fixed.Creation.Walk", "Lift.VyperNonreentrantDeployed.Fixed.Creation.Deploy", "Lift.VyperNonreentrantDeployed.Fixed.Clone.Input", "Lift.VyperNonreentrantDeployed.Fixed.Clone.Cert", "Lift.VyperNonreentrantDeployed.Fixed.Clone.Check", "Lift.VyperNonreentrantDeployed.Fixed.Clone.Walk", "Lift.VyperNonreentrantDeployed.Fixed.Clone.Deploy", "Lift.VyperNonreentrantDeployed.Fixed.Reach.World", "Lift.VyperNonreentrantDeployed.Fixed.Reach.Deploy", "Lift.VyperNonreentrantDeployed.Fixed.Reach.Exact", "Lift.VyperNonreentrantDeployed.Fixed.Init.World", "Lift.VyperNonreentrantDeployed.Fixed.Init.Proxy", "Lift.VyperNonreentrantDeployed.Fixed.Init.Run", "Lift.VyperNonreentrantDeployed.Fixed.Init.Top", "Lift.VyperNonreentrantDeployed.Fixed.Init.OracleRun", "Lift.VyperNonreentrantDeployed.Fixed.Init.OracleTop", "Lift.VyperNonreentrantDeployed.Fixed.Reach.Init", "Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Input", "Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Cert", "Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Check", "Lift.VyperNonreentrantDeployed.Vulnerable.Creation.State", "Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Walk", "Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Deploy", "Lift.VyperNonreentrantDeployed.Vulnerable.Clone.Input", "Lift.VyperNonreentrantDeployed.Vulnerable.Clone.Cert", "Lift.VyperNonreentrantDeployed.Vulnerable.Clone.Check", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.World", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Deploy", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.InitSetup", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.InitRun", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.InitTop", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Init", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Fund",          "Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Cert", "Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Check", "Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation.Input", "Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation.Cert", "Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation.Check", "Lift.VyperNonreentrantDeployed.Vulnerable.AttackerR.Creation.Deploy", "Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Cert", "Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Check", "Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.Input", "Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.Cert", "Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.Check", "Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.Creation.Deploy", "Lift.VyperNonreentrantDeployed.Fixed.Fund.World", "Lift.VyperNonreentrantDeployed.Fixed.Fund.Root", "Lift.VyperNonreentrantDeployed.Fixed.Fund.Create", "Lift.VyperNonreentrantDeployed.Fixed.Fund.Approve", "Lift.VyperNonreentrantDeployed.Fixed.Fund.AddRun", "Lift.VyperNonreentrantDeployed.Fixed.Fund.Add", "Lift.VyperNonreentrantDeployed.Fixed.Fund.Checkpoint", "Lift.VyperNonreentrantDeployed.Fixed.Exit.Run", "Lift.VyperNonreentrantDeployed.Fixed.Exit.Frames", "Lift.VyperNonreentrantDeployed.Fixed.Exit.Top", "Lift.VyperNonreentrantDeployed.Fixed.Exit.Main", "Lift.VyperNonreentrantDeployed.Fixed.Exit.Capstone", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.AddSetup", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.AddRun", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.AddTop", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Approve", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Checkpoint", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Violation", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReRun1", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReRun2", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReRun3", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReAdd", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolCallbackRun", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolCallback", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveSpec", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun1", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun2", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun3", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRootRun", "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRoot"],
    # Circle's USDC on mainnet: the FiatTokenProxy, the FiatTokenV2_2 implementation and the
    # SignatureChecker library it reaches by DELEGATECALL (usdc-weth9-pair-composition-v1).
    "usdc": [
        "Lift.Usdc.Book",
        "Lift.Usdc.ImplFp",
        "Lift.Usdc.ImplFp.Ann",
        "Lift.Usdc.ImplWs",
        "Lift.Usdc.ImplWs.Ann",
        "Lift.Usdc.ImplWs.Check",
        "Lift.Usdc.ImplWs.Check0",
        "Lift.Usdc.ImplWs.Check1",
        "Lift.Usdc.ImplWs.Check2",
        "Lift.Usdc.ImplWs.Check3",
        "Lift.Usdc.ImplFp.Check",
        "Lift.Usdc.ImplFp.Check0",
        "Lift.Usdc.ImplFp.Check1",
        "Lift.Usdc.ImplFp.Check2",
        "Lift.Usdc.ImplFp.Check3",
        "Lift.Usdc.Constants",
        "Lift.Usdc.Decode",
        "Lift.Usdc.Families",
        "Lift.Usdc.FiniteFootprint",
        "Lift.Usdc.Footprint",
        "Lift.Usdc.HistoricalMappingKeys",
        "Lift.Usdc.V1BlacklistReach",
        "Lift.Usdc.V1InitializerHistory",
        "Lift.Usdc.V1WriteFamilies",
        "Lift.Usdc.V1WriteApart",
        "Lift.Usdc.V1RetainedContext",
        "Lift.Usdc.V1RetainedAllowanceZero",
        "Lift.Usdc.V1TransactionContinuity",
        "Lift.Usdc.V1HistoryContinuity",
        "Lift.Usdc.V1MidHistoryContinuity",
        "Lift.Usdc.V1MainnetContinuity",
        "Lift.Usdc.V1ReceiptContinuity",
        "Lift.Usdc.V1ReceiptAllowanceZero",
        "Lift.Usdc.V1ConstructorReceiptZero",
        "Lift.Usdc.V1MappingTouches",
        "Lift.Usdc.V1ApproveReach",
        "Lift.Usdc.V1ApproveRetainedLog",
        "Lift.Usdc.V1ApproveRetainedLogReceipt",
        "Lift.Usdc.V1BurnReach",
        "Lift.Usdc.V1BurnMappingTouches",
        "Lift.Usdc.V1MintReach",
        "Lift.Usdc.V1MintMappingTouches",
        "Lift.Usdc.V1TransferFromReach",
        "Lift.Usdc.V1TransferFromNonIncReach",
        "Lift.Usdc.V1TransferFromNonInc",
        "Lift.Usdc.V1TransferFromMappingTouches",
        "Lift.Usdc.V1TransferReach",
        "Lift.Usdc.V1TransferMappingTouches",
        "Lift.Usdc.V1ApproveMappingTouches",
        "Lift.Usdc.V2ApproveReach",
        "Lift.Usdc.V2ApproveMappingTouches",
        "Lift.Usdc.V22MintReach",
        "Lift.Usdc.V22MintMappingTouches",
        "Lift.Usdc.V22TransferReach",
        "Lift.Usdc.V22TransferMappingTouches",
        "Lift.Usdc.V2_1TransferReach",
        "Lift.Usdc.V2_1TransferMappingTouches",
        "Lift.Usdc.V2_1MintReach",
        "Lift.Usdc.V2_1MintMappingTouches",
        "Lift.Usdc.OldTransferBodyReach",
        "Lift.Usdc.OldTransferFromCallee",
        "Lift.Usdc.OldTransferFromEntry",
        "Lift.Usdc.V22TransferFromCallee",
        "Lift.Usdc.V22TransferFromEntry",
        "Lift.Usdc.V22TransferFromAllowance",
        "Lift.Usdc.V22TransferFromContinuation",
        "Lift.Usdc.V22TransferFromMappingTouches",
        "Lift.Usdc.V21InitializerReach",
        "Lift.Usdc.V22InitializerReach",
        "Lift.Usdc.V21InitializerMappingTouches",
        "Lift.Usdc.V22InitializerMappingTouches",
        "Lift.Usdc.OldTransferFromAllowance",
        "Lift.Usdc.V2TransferReach",
        "Lift.Usdc.V2TransferWithAuthorizationReach",
        "Lift.Usdc.V22ReceiveWithAuthorizationBytesMappingTouches",
        "Lift.Usdc.V22ReceiveWithAuthorizationBytesReach",
        "Lift.Usdc.V22ReceiveWithAuthorizationMappingTouches",
        "Lift.Usdc.V22ReceiveWithAuthorizationReach",
        "Lift.Usdc.V22TransferWithAuthorizationBytesMappingTouches",
        "Lift.Usdc.V22TransferWithAuthorizationBytesReach",
        "Lift.Usdc.V22TransferWithAuthorizationMappingTouches",
        "Lift.Usdc.V22TransferWithAuthorizationReach",
        "Lift.Usdc.V2TransferWithAuthorizationMappingTouches",
        "Lift.Usdc.V2_1ReceiveWithAuthorizationMappingTouches",
        "Lift.Usdc.V2_1ReceiveWithAuthorizationReach",
        "Lift.Usdc.V2_1TransferWithAuthorizationMappingTouches",
        "Lift.Usdc.V2_1TransferWithAuthorizationReach",
        "Lift.Usdc.V2TransferFromCallee",
        "Lift.Usdc.V2TransferFromEntry",
        "Lift.Usdc.V2TransferFromContinuation",
        "Lift.Usdc.V2TransferFromCreditHashes",
        "Lift.Usdc.V2_1TransferFromContinuation",
        "Lift.Usdc.V2_1TransferFromCreditHashes",
        "Lift.Usdc.V2TransferMappingTouches",
        "Lift.Usdc.V22ConfigureMinterReach",
        "Lift.Usdc.V22ConfigureMinterMappingTouches",
        "Lift.Usdc.V2_1ConfigureMinterReach",
        "Lift.Usdc.V2_1ConfigureMinterMappingTouches",
        "Lift.Usdc.V2MintReach",
        "Lift.Usdc.V2MintMappingTouches",
        "Lift.Usdc.V2ConfigureMinterReach",
        "Lift.Usdc.V2ConfigureMinterMappingTouches",
        "Lift.Usdc.V2BlacklistMappingTouches",
        "Lift.Usdc.V22BlacklistReach",
        "Lift.Usdc.V22BlacklistMappingTouches",
        "Lift.Usdc.V2BlacklistReach",
        "Lift.Usdc.ModernCallerMappingTouches",
        "Lift.Usdc.ModernCancelMappingTouches",
        "Lift.Usdc.ModernCancelReach",
        "Lift.Usdc.ModernRemoveMinterReach",
        "Lift.Usdc.ModernBurnStores",
        "Lift.Usdc.V22BurnNonIncBodies",
        "Lift.Usdc.V22BurnNonIncReach",
        "Lift.Usdc.OldBurnNonIncCallees",
        "Lift.Usdc.OldBurnNonIncBodies",
        "Lift.Usdc.ModernBurnNonIncReach",
        "Lift.Usdc.ModernCallerHashBodies",
        "Lift.Usdc.V2_1PermitReach",
        "Lift.Usdc.V2_1PermitMappingTouches",
        "Lift.Usdc.V2_1AllowanceWriteLocality",
        "Lift.Usdc.V2PermitReach",
        "Lift.Usdc.V2PermitMappingTouches",
        "Lift.Usdc.V2AllowanceSetterReach",
        "Lift.Usdc.V2OwnerAuthorizationReach",
        "Lift.Usdc.V2OwnerAuthorizationMappingTouches",
        "Lift.Usdc.V2AllowanceWriteLocality",
        "Lift.Usdc.ModernCallerReach",
        "Lift.Usdc.ModernMinterFamilies",
        "Lift.Usdc.ModernTransferFromSites",
        "Lift.Usdc.OldTransferFromMappingTouches",
        "Lift.Usdc.ModernWriteFamilies",
        "Lift.Usdc.FootprintLedger",
        "Lift.Usdc.Governance",
        "Lift.Usdc.Hist",
        "Lift.Usdc.HistoryFamily",
        "Lift.Usdc.HistoryFamilyProxy",
        "Lift.Usdc.HistoryOwner",
        "Lift.Usdc.HistoryReplay",
        "Lift.Usdc.HistoryReplayFrames",
        "Lift.Usdc.HistorySlots",
        "Lift.Usdc.HistorySlotsCore",
        "Lift.Usdc.HistorySlotsFrames",
        "Lift.Usdc.HistorySlotsRescue",
        "Lift.Usdc.UpgraderHelperV2.Cert",
        "Lift.Usdc.UpgraderHelperV2.Check",
        "Lift.Usdc.UpgraderHelperV2_2.Cert",
        "Lift.Usdc.UpgraderHelperV2_2.Check",
        "Lift.Usdc.UpgraderV2.Cert",
        "Lift.Usdc.UpgraderV2.Check",
        "Lift.Usdc.UpgraderV2_1.Cert",
        "Lift.Usdc.UpgraderV2_1.Check",
        "Lift.Usdc.UpgraderV2_2.Cert",
        "Lift.Usdc.UpgraderV2_2.Check",
        "Lift.Usdc.Impl.Cert",
        "Lift.Usdc.Impl.Check",
        "Lift.Usdc.Impl.CheckPart0",
        "Lift.Usdc.Impl.CheckPart1",
        "Lift.Usdc.Impl.CheckPart2",
        "Lift.Usdc.Impl.CheckPart3",
        "Lift.Usdc.Impl.CheckTries",
        "Lift.Usdc.Impl.Contract",
        "Lift.Usdc.Impl.Jumps",
        "Lift.Usdc.ImplV1.Cert",
        "Lift.Usdc.ImplV1.MinterPcPatterns",
        "Lift.Usdc.ImplV1.MinterPcSources",
        "Lift.Usdc.V1MinterReach",
        "Lift.Usdc.V1ConfigureMinterReach",
        "Lift.Usdc.V1MinterHashOccurrences",
        "Lift.Usdc.V1MinterMappingTouches",
        "Lift.Usdc.ImplV1.Check",
        "Lift.Usdc.ImplV1.CheckPart0",
        "Lift.Usdc.ImplV1.CheckPart1",
        "Lift.Usdc.ImplV1.CheckPart2",
        "Lift.Usdc.ImplV1.CheckPart3",
        "Lift.Usdc.ImplV1.CheckTries",
        "Lift.Usdc.ImplV1.Jumps",
        "Lift.Usdc.ImplV2.Cert",
        "Lift.Usdc.ImplV2.Check",
        "Lift.Usdc.ImplV2.CheckPart0",
        "Lift.Usdc.ImplV2.CheckPart1",
        "Lift.Usdc.ImplV2.CheckPart2",
        "Lift.Usdc.ImplV2.CheckPart3",
        "Lift.Usdc.ImplV2.CheckTries",
        "Lift.Usdc.ImplV2.Jumps",
        "Lift.Usdc.ImplV2_1.Cert",
        "Lift.Usdc.ImplV2_1.Check",
        "Lift.Usdc.ImplV2_1.CheckPart0",
        "Lift.Usdc.ImplV2_1.CheckPart1",
        "Lift.Usdc.ImplV2_1.CheckPart2",
        "Lift.Usdc.ImplV2_1.CheckPart3",
        "Lift.Usdc.ImplV2_1.CheckTries",
        "Lift.Usdc.ImplV2_1.Jumps",
        "Lift.Usdc.AllowLocality",
        "Lift.Usdc.AllowLocalityInit",
        "Lift.Usdc.AllowLocalityV2_2",
        "Lift.Usdc.AllowLocalityHistory",
        "Lift.Usdc.AllowLocalitySstore",
        "Lift.Usdc.ProxySafeFrames",
        "Lift.Usdc.ProxyReachH",
        "Lift.Usdc.ProxyRawCallers",
        "Lift.Usdc.ProxyContextCodes",
        "Lift.Usdc.ImplV1Lifetime",
        "Lift.Usdc.AllowanceRawHistory",
        "Lift.Usdc.ProxySstoreH",
        "Lift.Usdc.ProxyUpgradeLog",
        "Lift.Usdc.ProxyCommittedUpgradeLog",
        "Lift.Usdc.ProxyRetainedContextCodes",
        "Lift.Usdc.ProxyRetainedNoDel",
        "Lift.Usdc.ProxyWritesHistory",
        "Lift.Usdc.InitReach",
        "Lift.Usdc.InitReachV2",
        "Lift.Usdc.InitReachV2_1",
        "Lift.Usdc.InitReachV2_2", "Lift.Usdc.SelTrees",
        "Lift.Usdc.InitReach06",
        "Lift.Usdc.InitReachV1",
        "Lift.Usdc.InitV1KeyBounds",
        "Lift.Usdc.InitV1ConcreteBounds",
        "Lift.Usdc.HistoricalBloomExclusion",
        "Lift.Usdc.InitRowsHistory",
        "Lift.Usdc.GovernanceHistory",
        "Lift.Usdc.InitializerClearing",
        "Lift.Usdc.OldInitializerEffects",
        "Lift.Usdc.OldInitializerV1Clearing",
        "Lift.Usdc.OldInitializerV1Payload",
        "Lift.Usdc.OldInitializerV1Staging",
        "Lift.Usdc.OldInitializerV1Callee",
        "Lift.Usdc.OldInitializerV1Root",
        "Lift.Usdc.ImplV1Ws",
        "Lift.Usdc.ImplV1Ws.Ann",
        "Lift.Usdc.ImplV1Ws.Check",
        "Lift.Usdc.ImplV1Ws.Check0",
        "Lift.Usdc.ImplV1Ws.Check1",
        "Lift.Usdc.ImplV1Ws.Check2",
        "Lift.Usdc.ImplV1Ws.Check3",
        "Lift.Usdc.ImplV2Ws",
        "Lift.Usdc.ImplV2Ws.Ann",
        "Lift.Usdc.ImplV2Ws.Check",
        "Lift.Usdc.ImplV2Ws.Check0",
        "Lift.Usdc.ImplV2Ws.Check1",
        "Lift.Usdc.ImplV2Ws.Check2",
        "Lift.Usdc.ImplV2Ws.Check3",
        "Lift.Usdc.ImplV2_1Ws",
        "Lift.Usdc.ImplV2_1Ws.Ann",
        "Lift.Usdc.ImplV2_1Ws.Check",
        "Lift.Usdc.ImplV2_1Ws.Check0",
        "Lift.Usdc.ImplV2_1Ws.Check1",
        "Lift.Usdc.ImplV2_1Ws.Check2",
        "Lift.Usdc.ImplV2_1Ws.Check3",
        "Lift.Usdc.ImplFrames",
        "Lift.Usdc.ImplSpawns",
        "Lift.Usdc.Lib.Cert",
        "Lift.Usdc.Lib.Check",
        "Lift.Usdc.Lib.Contract",
        "Lift.Usdc.Lib.Jumps",
        "Lift.Usdc.LibSpawns",
        "Lift.Usdc.Model",
        "Lift.Usdc.ModelControls",
        "Lift.Usdc.ModelLaws",
        "Lift.Usdc.PermitQueryV2_1",
        "Lift.Usdc.PermitRowRecoveryV2_1",
        "Lift.Usdc.PermitRowPrefixV2_1",
        "Lift.Usdc.PermitRowNativeV2_1",
        "Lift.Usdc.OwnerQueriesV2",
        "Lift.Usdc.OldRecoveryRelevance",
        "Lift.Usdc.RetainedOldRecovery",
        "Lift.Usdc.RetainedAllowanceWrites",
        "Lift.Usdc.Proxy.Cert",
        "Lift.Usdc.Proxy.Check",
        "Lift.Usdc.Proxy.Contract",
        "Lift.Usdc.Proxy.Control",
        "Lift.Usdc.Proxy.Jumps",
        "Lift.Usdc.ProxyCreation.Cert",
        "Lift.Usdc.ProxyCreation.Check",
        "Lift.Usdc.ProxyCreation.Jumps",
        "Lift.Usdc.ProxyCreation.CodeSize",
        "Lift.Usdc.ProxyCreation.RuntimeReturn",
        "Lift.Usdc.ProxyCreation.RuntimeWindow",
        "Lift.Usdc.ProxyCreation.ConstantsCheck",
        "Lift.Usdc.ProxyCreation.Prefix",
        "Lift.Usdc.ProxyCreation.Effects",
        "Lift.Usdc.ProxyCreation.Settlement",
        "Lift.Usdc.ProxyCreation.Transaction",
        "Lift.Usdc.ProxyCreation.ForeignCode",
        "Lift.Usdc.ProxyCreation.HistoryCut",
        "Lift.Usdc.ProxyCreation.HistoryFrame",
        "Lift.Usdc.ProxyForward",
        "Lift.Usdc.ProxyHalt",
        "Lift.Usdc.ProxyOk",
        "Lift.Usdc.ProxyReach",
        "Lift.Usdc.ProxyWalk",
        "Lift.Usdc.RecoveryV2",
        "Lift.Usdc.RecoveryV2_1",
        "Lift.Usdc.RefineAdmin",
        "Lift.Usdc.RefineAdminBits",
        "Lift.Usdc.RefineAdminBodies",
        "Lift.Usdc.RefineAdminBodiesMint",
        "Lift.Usdc.RefineAdminCallees",
        "Lift.Usdc.RefineAdminDispatch",
        "Lift.Usdc.RefineAdminLedger",
        "Lift.Usdc.RefineAdminReach",
        "Lift.Usdc.RefineAdminRescue",
        "Lift.Usdc.RefineAdminRun",
        "Lift.Usdc.RefineDispatch",
        "Lift.Usdc.RefineDispatchCheck",
        "Lift.Usdc.RefineShape",
        "Lift.Usdc.RefineSigned",
        "Lift.Usdc.RefineSignedAuth",
        "Lift.Usdc.RefineSignedAuthChecks",
        "Lift.Usdc.RefineSignedAuthFrames",
        "Lift.Usdc.RefineSignedAuthWalk",
        "Lift.Usdc.RefineSignedCallees",
        "Lift.Usdc.RefineSignedPermit",
        "Lift.Usdc.RefineSignedPermitCore",
        "Lift.Usdc.RefineSignedPermitFrames",
        "Lift.Usdc.RefineSignedPermitNodes",
        "Lift.Usdc.RefineTransfer",
        "Lift.Usdc.RefineTransferCallees",
        "Lift.Usdc.RefineTransferDecode",
        "Lift.Usdc.RefineTransferDispatch",
        "Lift.Usdc.RefineTransferNodes",
        "Lift.Usdc.ShuffleSegments",
        "Lift.Usdc.SignedSkip",
        "Lift.Usdc.Slots",
        "Lift.Usdc.HistoryEnd",
        "Lift.Usdc.HistoryEndFoot",
        "Lift.Usdc.FiniteFootprintF",
        "Lift.Usdc.HistFCore",
        "Lift.Usdc.HistFFacts",
        "Lift.Usdc.HistFSlots",
        "Lift.Usdc.CreationHistory",
        "Lift.Usdc.HistoryAnchorObservationData",
        "Lift.Usdc.ImplV1Creation.Bindings",
        "Lift.Usdc.ImplV1Creation.Cert",
        "Lift.Usdc.ImplV1Creation.Check",
        "Lift.Usdc.ImplV1Creation.Jumps",
        "Lift.Usdc.ImplV1Creation.Observation",
        "Lift.Usdc.ImplV1Creation.ObservationData",
        "Lift.Usdc.ImplV1Creation.SignedInput",
        "Lift.Usdc.ImplV1Creation.SigningEncoding",
        "Lift.Usdc.ImplV1Creation.SigningHash",
        "Lift.Usdc.ImplV1Origin",
        "Lift.Usdc.ImplV2Creation.Bindings",
        "Lift.Usdc.ImplV2Creation.Cert",
        "Lift.Usdc.ImplV2Creation.Check",
        "Lift.Usdc.ImplV2Creation.Jumps",
        "Lift.Usdc.ImplV2Creation.Observation",
        "Lift.Usdc.ImplV2Creation.ObservationData",
        "Lift.Usdc.ImplV2Creation.SignedInput",
        "Lift.Usdc.ImplV2Creation.SigningEncoding",
        "Lift.Usdc.ImplV2Creation.SigningHash",
        "Lift.Usdc.ImplV2_1Creation.Bindings",
        "Lift.Usdc.ImplV2_1Creation.Cert",
        "Lift.Usdc.ImplV2_1Creation.Check",
        "Lift.Usdc.ImplV2_1Creation.Jumps",
        "Lift.Usdc.ImplV2_1Creation.Observation",
        "Lift.Usdc.ImplV2_1Creation.ObservationData",
        "Lift.Usdc.ImplV2_1Creation.SignedInput",
        "Lift.Usdc.ImplV2_1Creation.SigningEncoding",
        "Lift.Usdc.ImplV2_1Creation.SigningHash",
        "Lift.Usdc.ImplV2_2Creation.Bindings",
        "Lift.Usdc.ImplV2_2Creation.Cert",
        "Lift.Usdc.ImplV2_2Creation.Check",
        "Lift.Usdc.ImplV2_2Creation.Jumps",
        "Lift.Usdc.ImplV2_2Creation.Observation",
        "Lift.Usdc.ImplV2_2Creation.ObservationData",
        "Lift.Usdc.ImplV2_2Creation.SignedInput",
        "Lift.Usdc.ImplV2_2Creation.SigningEncoding",
        "Lift.Usdc.ImplV2_2Creation.SigningHash",
        "Lift.Usdc.LibCreation.Bindings",
        "Lift.Usdc.LibCreation.Cert",
        "Lift.Usdc.LibCreation.Check",
        "Lift.Usdc.LibCreation.Observation",
        "Lift.Usdc.LibCreation.ObservationData",
        "Lift.Usdc.LibCreation.Receipt",
        "Lift.Usdc.LibCreation.Settlement",
        "Lift.Usdc.LibCreation.SignedInput",
        "Lift.Usdc.LibCreation.SigningEncoding",
        "Lift.Usdc.LibCreation.SigningHash",
        "Lift.Usdc.ProxyCompleteAvailable",
        "Lift.Usdc.V22AllowanceWriteLocality",
        "Lift.Usdc.V22PermitEntry",
        "Lift.Usdc.V22PermitMappingTouches",
        "Lift.Usdc.V22PermitReach",
    ],
}

# Frozen byte producer and its conditional original-cut consumer.
SHARED += ["ExecutionBodyTransactionCut"]
SHARED += ["Lift.LegacyRecover"]
CONTRACTS["usdc"].extend([
    "Lift.Usdc.HistoryAnchorBody",
    "Lift.Usdc.HistoryAnchorCSigningHash",
    "Lift.Usdc.HistoryAnchorCSender",
    "Lift.Usdc.HistoryAnchorCCode",
    "Lift.Usdc.HistoryAnchorBodyGenerated",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC00",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC01",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC02",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC03",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC04",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC05",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC06",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC07",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC08",
    "Lift.Usdc.HistoryAnchorBodyGeneratedC09",
    "Lift.Usdc.HistoryAnchorBodyGeneratedD00",
    "Lift.Usdc.HistoryAnchorBodyGeneratedD01",
    "Lift.Usdc.HistoryAnchorBodyGeneratedD02",
    "Lift.Usdc.HistoryAnchorBodyGeneratedD03",
    "Lift.Usdc.HistoryAnchorBodyGeneratedD04",
    "Lift.Usdc.HistoryAnchorBodyGeneratedD05",
    "Lift.Usdc.HistoryAnchorBodyGeneratedD06",
    "Lift.Usdc.HistoryAnchorBodyInput",
])

# Finite hash separation, the kernel trie-root twin with its node-hash certificate, and header
# binding (weth9-observation-binding-v1): contract-neutral.
SHARED += ["Separated", "TrieKernel", "HeaderBinding"]


# The root-frame and final-composition modules extend the deployed contract classification.
CONTRACTS["vyper-nonreentrant-deployed"].extend([
    "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolTopRun",
    "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolTop",
    "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemoveRun4",
    "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRemove",
    "Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolFinal",
])






CONTRACTS["usdc"].extend(['Lift.Usdc.TransferLiveImpl', 'Lift.Usdc.TransferLiveProxy', 'Lift.Usdc.TransferLiveFrame', 'Lift.Usdc.TransferLiveFacts'])
SHARED += ["Lift.AccumulatedWalk", "Lift.GasField"]
SHARED += ["SyntheticSystemWorld", "SyntheticBpo2Envelope"]


SHARED += ["ExecutionTraceMessageRoots"]
CONTRACTS["usdc"].append("Lift.Usdc.AllowanceQuiet")

SHARED += ["Lift.CallMessageFacts", "Lift.CalldataWords", "Lift.ExactWalkStaticCallChild"]

SHARED += ["ExecutionTargetPrefix"]

# Fixed synthetic 299-byte token fixture, shared without V± instance worlds.
SHARED += ['Lift.Token20.Cert', 'Lift.Token20.Check', 'Lift.Token20.Creation.Cert', 'Lift.Token20.Creation.Check', 'Lift.Token20.Creation.Deploy', 'Lift.Token20.Creation.Input', 'Lift.Token20.Frame', 'Lift.Token20.Run', 'Lift.Token20.RunBalance', 'Lift.Token20.RunTransfer', 'Lift.Token20.RunTransferFrom']

# Execution facts over selected-domain histories, transaction-item transport and the block-hash
# binding, and the frame-chain, coin-frame, root-standing, write-site and walk-cost kits
# (curve-3pool-flagship-v1): contract-neutral. `Lift.CodeImage` keeps a pinned `Lift.Usdc`
# constant name, moved here because a shared kit needs it; the definition names no contract.
SHARED += [
    "BlockHashBinding",
    "ExecutionHistoryInFrameEnv",
    "ExecutionHistoryInPreCancun",
    "ExecutionHistoryInSystemConfined",
    "ExecutionHistoryMuirCut",
    "ExecutionMidHistoryInFrameTime",
    "ExecutionMidHistoryInOwnCode",
    "ExecutionMidHistoryInRootCallers",
    "ExecutionMidWindowIn",
    "ExecutionReceiptLogLink",
    "ExecutionWholeFrameAccountingIn",
    "TransactionItemTransport",
    "Lift.ApprovalLog",
    "Lift.BalanceLocality",
    "Lift.ChainNoExec",
    "Lift.ChainStatic",
    "Lift.ChildCell",
    "Lift.CodeImage",
    "Lift.CoinFrame",
    "Lift.CoinKeys",
    "Lift.ExactCallFloor",
    "Lift.ExecFreeLogs",
    "Lift.ForeignKeep",
    "Lift.FrameChain",
    "Lift.HistFrameWalk",
    "Lift.HistIdentityCall",
    "Lift.InvWalkLegacy",
    "Lift.LinearRuntimeSafety",
    "Lift.LogFilterPremises",
    "Lift.PoolCoinSel",
    "Lift.ReachKinds",
    "Lift.RootChain",
    "Lift.RootReady",
    "Lift.RootStanding",
    "Lift.ViewChain",
    "Lift.WalkCost",
    "Lift.WalkCostExact",
    "Lift.WalkFpMove",
    "Lift.WriteSiteMapping",
    "Lift.WriteSiteRowClass",
]

# DAI (solc 0.5.12) and USDT (TetherToken, solc 0.4.x), deployed bytes in the 3pool's span: lifted
# runtime, write-site checker, frame laws, forward laws and exact cost (curve-3pool-flagship-v1).
# Their per-coin modules under `Lift.CurveCoins` are theirs: no module here imports another coin.
CONTRACTS["dai"] = [
    "Lift.CurveCoins.ApprovalLogsDai",
    "Lift.CurveCoins.BalanceAnswers",
    "Lift.CurveCoins.Dai",
    "Lift.CurveCoins.DaiLocality",
    "Lift.CurveCoins.DaiPermit",
    "Lift.CurveCoins.DaiPremises",
    "Lift.CurveCoins.KeepDai",
    "Lift.Dai.Cert",
    "Lift.Dai.Check",
    "Lift.Dai.CheckPart0",
    "Lift.Dai.CheckPart1",
    "Lift.Dai.CheckTries",
    "Lift.Dai.Jumps",
    "Lift.DaiExact",
    "Lift.DaiForward",
    "Lift.DaiFrames",
    "Lift.DaiWs",
    "Lift.DaiWs.Ann",
    "Lift.DaiWs.Check",
    "Lift.DaiWs.Check0",
    "Lift.DaiWs.Check1",
]
CONTRACTS["usdt"] = [
    "Lift.CurveCoins.ApprovalLogsUsdt",
    "Lift.CurveCoins.KeepUsdt",
    "Lift.CurveCoins.Usdt",
    "Lift.CurveCoins.UsdtLocality",
    "Lift.CurveCoins.UsdtPremises",
    "Lift.CurveCoins.UsdtQuiet",
    "Lift.Usdt.Cert",
    "Lift.Usdt.Check",
    "Lift.Usdt.CheckPart0",
    "Lift.Usdt.CheckPart1",
    "Lift.Usdt.CheckTries",
    "Lift.Usdt.Jumps",
    "Lift.UsdtExact",
    "Lift.UsdtForward",
    "Lift.UsdtForwardLaws",
    "Lift.UsdtForwardSteps",
    "Lift.UsdtFrames",
    "Lift.UsdtOwnerFrames",
    "Lift.UsdtWs",
    "Lift.UsdtWs.Ann",
    "Lift.UsdtWs.Check",
    "Lift.UsdtWs.Check0",
    "Lift.UsdtWs.Check1",
]
# USDC's implementation-version laws, entry chain and its per-coin modules (curve-3pool-flagship-v1).
CONTRACTS["usdc"].extend([
    "Lift.CurveCoins.ApprovalLogsUsdcV1",
    "Lift.CurveCoins.ApprovalLogsUsdcV2",
    "Lift.CurveCoins.ApprovalLogsUsdcV2_1",
    "Lift.CurveCoins.KeepUsdc",
    "Lift.CurveCoins.UsdcV2",
    "Lift.CurveCoins.UsdcV2_1",
    "Lift.CurveCoins.UsdcV2_2",
    "Lift.Usdc.AuthLog",
    "Lift.Usdc.EntryChain",
    "Lift.Usdc.EntryChainProof",
    "Lift.Usdc.EntryChainRoots",
    "Lift.Usdc.EntryChainScan",
    "Lift.Usdc.EntryChainSettled",
    "Lift.Usdc.EntryJoin",
    "Lift.Usdc.EntryLaw",
    "Lift.Usdc.EntryLawProxy",
    "Lift.Usdc.EntryLawProxyHalt",
    "Lift.Usdc.EntryLawV2",
    "Lift.Usdc.EntryLawV22",
    "Lift.Usdc.EntryLawV2Walks",
    "Lift.Usdc.EntryLawV2_1Walks",
    "Lift.Usdc.EntryLawWord",
    "Lift.Usdc.EntryPositional",
    "Lift.Usdc.EntryQuiet",
    "Lift.Usdc.EntryRescue",
    "Lift.Usdc.EntryTarget",
    "Lift.Usdc.InitializerKeeps",
    "Lift.Usdc.ProxyLands",
    "Lift.Usdc.SignedLogs",
    "Lift.Usdc.SignedSkipH",
    "Lift.Usdc.V22BalanceLaws",
    "Lift.Usdc.V22Forward",
    "Lift.Usdc.V2Answer",
    "Lift.Usdc.V2Family",
    "Lift.Usdc.V2Forward",
    "Lift.Usdc.V2Frames",
    "Lift.Usdc.V2_1Answer",
    "Lift.Usdc.V2_1Forward",
    "Lift.Usdc.V2_1Frames",
    "Lift.Usdc.VersionStands",
    "Lift.UsdcExact",
])
# The 3pool's and 3Crv's historical transactions and generated creation-block families, histories
# that start mid-block, floor walks and refutation run (curve-3pool-flagship-v1). Generated block
# modules follow `Lift.Weth9.Creation.Block.*` at tag corpus-v1-20261105.
CONTRACTS["curve-3pool"].extend([
    "Lift.Curve3Pool.AmpHistoryMid",
    "Lift.Curve3Pool.Creation.Block.Header",
    "Lift.Curve3Pool.Creation.Block.ReceiptCert0",
    "Lift.Curve3Pool.Creation.Block.ReceiptCert1",
    "Lift.Curve3Pool.Creation.Block.ReceiptCert2",
    "Lift.Curve3Pool.Creation.Block.ReceiptData",
    "Lift.Curve3Pool.Creation.Block.ReceiptRoot",
    "Lift.Curve3Pool.Creation.Block.Slot",
    "Lift.Curve3Pool.Creation.Block.TxCert0",
    "Lift.Curve3Pool.Creation.Block.TxCert1",
    "Lift.Curve3Pool.Creation.Block.TxCert2",
    "Lift.Curve3Pool.Creation.Block.TxData",
    "Lift.Curve3Pool.Creation.Block.TxRoot",
    "Lift.Curve3Pool.Creation.HistoricalTx",
    "Lift.Curve3Pool.Creation.HistoricalTxTrace",
    "Lift.Curve3Pool.Creation.HistoricalWalk",
    "Lift.Curve3Pool.ExchangeFloorFrame",
    "Lift.Curve3Pool.HistoryMid",
    "Lift.Curve3Pool.HistoryWindow",
    "Lift.Curve3Pool.LadderH",
    "Lift.Curve3Pool.RemoveLiquidityFloorFrame",
    "Lift.Curve3Pool.RuntimeSafety",
    "Lift.Curve3Pool.StepCallFree",
    "Lift.Curve3Pool.U3ParamWitnesses",
    "Lift.Curve3Pool.VirtualPriceFallsRun",
    "Lift.Curve3Pool.Walk.ChildrenSel",
    "Lift.Curve3Pool.Walk.ExchangeFloorCores",
    "Lift.Curve3Pool.Walk.ExchangeFloorWalk",
    "Lift.Curve3Pool.Walk.KeepSel",
    "Lift.Curve3Pool.Walk.RemoveLiquidityFloorWalk",
    "Lift.CurveCoins.PoolFreshAtCreation",
])
CONTRACTS["curve-3crv"].extend([
    "Lift.Curve3Crv.Creation.Block.Header",
    "Lift.Curve3Crv.Creation.Block.ReceiptCert0",
    "Lift.Curve3Crv.Creation.Block.ReceiptCert1",
    "Lift.Curve3Crv.Creation.Block.ReceiptCert2",
    "Lift.Curve3Crv.Creation.Block.ReceiptCert3",
    "Lift.Curve3Crv.Creation.Block.ReceiptCert4",
    "Lift.Curve3Crv.Creation.Block.ReceiptData",
    "Lift.Curve3Crv.Creation.Block.ReceiptRoot",
    "Lift.Curve3Crv.Creation.Block.Slot",
    "Lift.Curve3Crv.Creation.Block.TxCert0",
    "Lift.Curve3Crv.Creation.Block.TxCert1",
    "Lift.Curve3Crv.Creation.Block.TxData",
    "Lift.Curve3Crv.Creation.Block.TxRoot",
    "Lift.Curve3Crv.Creation.BlockMinter.Header",
    "Lift.Curve3Crv.Creation.BlockMinter.ReceiptCert0",
    "Lift.Curve3Crv.Creation.BlockMinter.ReceiptCert1",
    "Lift.Curve3Crv.Creation.BlockMinter.ReceiptCert2",
    "Lift.Curve3Crv.Creation.BlockMinter.ReceiptCert3",
    "Lift.Curve3Crv.Creation.BlockMinter.ReceiptCert4",
    "Lift.Curve3Crv.Creation.BlockMinter.ReceiptData",
    "Lift.Curve3Crv.Creation.BlockMinter.ReceiptRoot",
    "Lift.Curve3Crv.Creation.BlockMinter.Slot",
    "Lift.Curve3Crv.Creation.BlockMinter.TxCert0",
    "Lift.Curve3Crv.Creation.BlockMinter.TxCert1",
    "Lift.Curve3Crv.Creation.BlockMinter.TxData",
    "Lift.Curve3Crv.Creation.BlockMinter.TxRoot",
    "Lift.Curve3Crv.HistFrameReady",
    "Lift.Curve3Crv.HistWindow",
    "Lift.Curve3Crv.SetMinterTx",
])

# EIP-8282 builder request contracts (deposit and exit): the lifted runtimes and init codes, their
# registered certificates, and the deployment through the shared CREATE2 factory walk. One family
# for the two contracts; it never imports another contract family, and the generic factory and
# runtime-install steps it uses are the shared modules registered just below.
SHARED += ["Lift.Create2Factory.Cert", "Lift.Create2Factory.Check", "Lift.Create2Factory.Code",
           "Lift.Create2Factory.Jumps", "Lift.Create2Factory.Walk", "Lift.RuntimeInstall"]
# Amsterdam walk-engine support (blanc-eip8282-builder-requests-v1 O6): the state-gas `SSTORE` and
# `SLOAD` steps and the top-level system-call envelope, contract-neutral. `CoveredFork` is not widened.
SHARED += ["Lift.AmsterdamWalk", "Lift.ExecCut", "Lift.TransactionAmsterdam", "Lift.SystemCallAmsterdam"]
# The two pushed-word facts of a request contract's dispatch and inhibitor guard.
SHARED += ["Lift.SystemCaller", "MemoryWindows"]
# The system path all four Amsterdam request contracts share (blanc-eip8282-builder-requests-v1 O9).
SHARED += ["Lift.RequestSystem.Dispatch", "Lift.RequestSystem.Path", "Lift.RequestSystem.Call",
           "Lift.RequestSystem.Output", "Lift.RequestSystem.BodySegs",
           "Lift.RequestSystem.PlainExcess", "Lift.SystemExecution.ConsolidationRequest.AmsterdamSystem"]
CONTRACTS["builder-request"] = [
    "Lift.BuilderRequest.Deposit.Code", "Lift.BuilderRequest.Deposit.Cert",
    "Lift.BuilderRequest.Deposit.Check", "Lift.BuilderRequest.Deposit.Jumps",
    "Lift.BuilderRequest.Deposit.Creation.Input", "Lift.BuilderRequest.Deposit.Creation.Cert",
    "Lift.BuilderRequest.Deposit.Creation.Check", "Lift.BuilderRequest.Deposit.Creation.Address",
    "Lift.BuilderRequest.Deposit.Creation.Deploy", "Lift.BuilderRequest.Deposit.FeeWindow",
    "Lift.BuilderRequest.Deposit.Submission", "Lift.BuilderRequest.Deposit.Frames",
    "Lift.BuilderRequest.FeePath", "Lift.BuilderRequest.QueueLayout",
    "Lift.BuilderRequest.Message", "Lift.BuilderRequest.Revert", "Lift.BuilderRequest.Transaction",
    "Lift.BuilderRequest.Deposit.Transaction", "Lift.BuilderRequest.Exit.Transaction",
    "Lift.BuilderRequest.TransactionWitness",
    "Lift.BuilderRequest.Deposit.Message", "Lift.BuilderRequest.Deposit.Revert",
    "Lift.BuilderRequest.Exit.Message", "Lift.BuilderRequest.Exit.Revert",
    "Lift.BuilderRequest.SystemPath", "Lift.BuilderRequest.SystemOutput",
    "Lift.BuilderRequest.Deposit.Fifo", "Lift.BuilderRequest.Exit.Fifo",
    "Lift.BuilderRequest.Latch", "Lift.BuilderRequest.Deposit.Latch",
    "Lift.BuilderRequest.Exit.Latch", "Lift.BuilderRequest.Deposit.Backlog",
    "Lift.BuilderRequest.Balances", "Lift.BuilderRequest.UserFrame",
    "Lift.BuilderRequest.Exit.Submission", "Lift.BuilderRequest.Exit.SubmissionAmsterdam",
    "Lift.BuilderRequest.Deposit.SubmissionAmsterdam",
    "Lift.BuilderRequest.UserFrameAmsterdam",
    "Lift.BuilderRequest.Deposit.System", "Lift.BuilderRequest.Deposit.SystemCall",
    "Lift.BuilderRequest.Exit.System", "Lift.BuilderRequest.Exit.SystemCall",
    "Lift.BuilderRequest.Exit.Frames",
    "Lift.BuilderRequest.Exit.Code", "Lift.BuilderRequest.Exit.Cert",
    "Lift.BuilderRequest.Exit.Check", "Lift.BuilderRequest.Exit.Jumps",
    "Lift.BuilderRequest.Exit.Creation.Input", "Lift.BuilderRequest.Exit.Creation.Cert",
    "Lift.BuilderRequest.Exit.Creation.Check", "Lift.BuilderRequest.Exit.Creation.Address",
    "Lift.BuilderRequest.Exit.Creation.Deploy",
]

# Explicit semantic ownership, not the union of existing imports. Abstract token
# interfaces do not add WETH9/USDC to PairToken/PairTwoToken; concrete instances
# do. Single-family token adapters and Curve replay adapters stay narrow. The
# Pair/USDC provenance bridges genuinely compose those two families; their
# current imports must not widen them to the WETH9 exhibit. Named exhibit kits
# retain their exhibit ownership until moved to a neutral shared owner.
# Withdrawal witnesses retain concrete canonical system operations through the
# shared SystemExecution owner; those operations add no standalone exhibit family.
# Each entry is a nonempty tuple of distinct CONTRACTS keys. Adding a composition
# declares its boundary here; no default family or production exception exists.
COMPOSITION = {
    "Composition.RequestPhaseAmsterdam": ('builder-request', 'withdrawal-request'),
    "Composition.WithdrawalRequestFeeCounterexample": ('withdrawal-request',),
    "Composition.WithdrawalRequestFeeRefutation": ('withdrawal-request',),
    "Composition.WithdrawalRequestFeeHeadline": ('withdrawal-request',),
    "Composition.WithdrawalRequestDrainControl": ('withdrawal-request',),
    "Composition.Curve3Pool3CrvCheckpoint": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3CrvTokenCore": ('curve-3crv',),
    "Composition.Curve3CrvPositional": ('curve-3crv',),
    "Composition.Curve3PoolSupplyFrames": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3PoolSupplyCalls": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3PoolSupplyStep": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3PoolSupply": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvU3": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3PoolCalleeLive": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3PoolCalleeExactProfiles": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvHeadlines": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvWorld": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvTxData": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvSigningEncoding": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvSigningHash": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvSigningRecover": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvBlock": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvCoinCalls": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvExRoot": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvTxFrame": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvTraceEnv": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvCapstoneModel": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvWorldAgrees": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvCoinExactTransport": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvCoinExact": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvCoinAnswers": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvCapstoneFrame": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvCapstoneTx": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvCapstone": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveWitness": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvExactAssembly": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvHeadlinesExact": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvExactWitness": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvExactLiteralWitness": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvExactLiteralHeadlines": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveConcrete": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveEndEntry": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveEndRL": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveEndOC": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveEndKeep": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveEndRLI": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveEndAL": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveEndKeepAL": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3Pool3CrvLiveEndKeepRLI": ('curve-3pool', 'curve-3crv'),
    "Composition.UsdcToken": ('usdc',),
    "Composition.UsdcTokenCore": ('usdc',),
    "Composition.UsdcTokenLive": ('usdc',),
    "Composition.UsdcTokenF": ('usdc',),
    "Composition.Curve3Pool3CrvCoinExactExit": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3Pool3CrvCoinExactFloor": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3Pool3CrvCoinExactSwap": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3Pool3CrvU3Mid": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBacked": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBackedDai": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBackedEnv": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBackedFlat": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBackedLedger": ('curve-3pool',),
    "Composition.Curve3PoolBackedModel": ('curve-3pool',),
    "Composition.Curve3PoolBackedUsdc": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBackedUsdt": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBackedWalk": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBackedWindow": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolBlockAnchor": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolCalleeFloorProfiles": ('curve-3pool', 'curve-3crv', 'usdt'),
    "Composition.Curve3PoolCoinChild": ('curve-3pool', 'curve-3crv'),
    "Composition.Curve3PoolCoinExactKit": ('curve-3pool', 'curve-3crv', 'usdt'),
    "Composition.Curve3PoolCoinExchange": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolCoinFloorKit": ('curve-3pool', 'curve-3crv', 'usdt'),
    "Composition.Curve3PoolCoinKeep": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolDaiCoin": ('curve-3pool', 'curve-3crv', 'dai'),
    "Composition.Curve3PoolDaiCoinExact": ('curve-3pool', 'curve-3crv', 'dai', 'usdt'),
    "Composition.Curve3PoolJointRoot": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolKeepAt": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolKeepHistory": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitCoins": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitCold": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitFits": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitMain": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolImbalanceMain": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolRemoveMessage": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitMoment": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitRequest": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitSites": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitTx": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitView": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolExitWorks": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapBack": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapBound": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapChain": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapCoins": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapCold": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapEval": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapFits": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolOneCoinMain": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapMain": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapPay": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapRequest": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSwapSites": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolAddCoins": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolAddCost": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolAddMain": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolAddRequest": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolPublic": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolPublicBridge": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolPublicEffects": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolPublicGas": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolPublicObservers": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolPublicPremises": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolPublicPrice": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolPublicTx": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolSupplyMid": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolUsdc22Coin": ('curve-3pool', 'curve-3crv', 'usdc'),
    "Composition.Curve3PoolUsdcCoin": ('curve-3pool', 'curve-3crv', 'usdc'),
    "Composition.Curve3PoolUsdcCoinExact": ('curve-3pool', 'curve-3crv', 'usdc', 'usdt'),
    "Composition.Curve3PoolUsdcEntryApart": ('curve-3pool', 'usdc'),
    "Composition.Curve3PoolUsdcProxy": ('curve-3pool', 'curve-3crv', 'usdc'),
    "Composition.Curve3PoolUsdcV2Coin": ('curve-3pool', 'curve-3crv', 'usdc'),
    "Composition.Curve3PoolUsdcV2_1Coin": ('curve-3pool', 'curve-3crv', 'usdc'),
    "Composition.Curve3PoolUsdtCoin": ('curve-3pool', 'curve-3crv', 'usdt'),
    "Composition.Curve3PoolUsdtCoinExact": ('curve-3pool', 'curve-3crv', 'usdt'),
    "Composition.Curve3PoolUsdtCoinExchange": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPrice": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceDeploy": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFalls": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsChain": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsData": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts0": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts1": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts10": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts2": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts3": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts4": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts5": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts6": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts7": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts8": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsFacts9": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFallsWorld": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceFrames": ('curve-3pool', 'curve-3crv', 'dai', 'usdc', 'usdt'),
    "Composition.Curve3PoolVirtualPriceModel": ('curve-3pool',),
    # Every joint owner is explicit; no family or shared module may import back.
}

ROOTS = ["Blanc", "Main"]

def composition_declaration_failures(declarations, contracts):
    """Validate the semantic declarations before any import can be admitted."""
    if not isinstance(declarations, dict) or not declarations:
        return ["COMPOSITION must be a nonempty module-to-family-tuple mapping"]
    failures = []
    for mod, families in declarations.items():
        if (not isinstance(mod, str) or not mod.startswith("Composition.")
                or not mod.removeprefix("Composition.")):
            failures.append(f"COMPOSITION key {mod!r} must name a Composition module")
        if not isinstance(families, tuple) or not families:
            failures.append(f"{mod}: declared families must be a nonempty tuple")
            continue
        seen = set()
        for family in families:
            if not isinstance(family, str) or family not in contracts:
                failures.append(f"{mod}: unknown declared contract family {family!r}")
            elif family in seen:
                failures.append(f"{mod}: duplicate declared contract family {family!r}")
            else:
                seen.add(family)
    return failures


def classify():
    """-> module -> category: shared, root, composition, or a contract family."""
    invalid = composition_declaration_failures(COMPOSITION, CONTRACTS)
    if invalid:
        raise SystemExit("REGRESSION — layering: " + "; ".join(invalid))
    owner = {}
    for group, category in (
        [(mod, "shared") for mod in SHARED]
        + [(mod, "root") for mod in ROOTS]
        + [(mod, "composition") for mod in COMPOSITION]
        + [(mod, name) for name, mods in CONTRACTS.items() for mod in mods]
    ):
        if group in owner:
            raise SystemExit(
                f"REGRESSION — layering: {group} classified twice in this script"
            )
        owner[group] = category
    return owner


def modules_on_disk(root):
    """-> module name -> path, for every Lean module in the repository.

    The walk under `Blanc/` is recursive and names a nested module the way an
    `import` statement spells it: `Blanc/Composition/X.lean` is
    `Composition.X`. A non-recursive listing here would let any module in a
    subdirectory escape check 1 -- and therefore every other check -- without
    anyone editing this file, which is exactly the silent escape check 1
    exists to prevent.
    """
    found = {}
    for name in ("Blanc.lean", "Main.lean"):
        path = os.path.join(root, name)
        if os.path.exists(path):
            found[name[: -len(".lean")]] = path
    src = os.path.join(root, "Blanc")
    for dirpath, dirnames, filenames in os.walk(src):
        dirnames.sort()
        for name in sorted(filenames):
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            relative = os.path.relpath(path, src)
            module = relative[: -len(".lean")].replace(os.sep, ".")
            found[module] = path
    return found


class HeaderParseError(Exception):
    """The lexical state of a module header cannot be established safely."""


class HeaderScanner:
    """The small, fail-closed subset of Lean's module-header parser this gate needs.

    Lean 4.32.1 defines a header as an optional `module`, optional `prelude`,
    and zero or more imports in `Lean/Parser/Module/Syntax.lean`.  This scanner
    deliberately does not parse the body: its first non-header command ends
    the scan.  It does, however, lex header trivia itself, because an import is
    allowed to cross physical lines and comments, while import-shaped text in a
    comment or body string is not an import.
    """

    def __init__(self, text):
        self.text = text
        self.i = 0

    def error(self, message):
        line = self.text.count("\n", 0, self.i) + 1
        raise HeaderParseError(f"{message} at header line {line}")

    def skip_trivia(self):
        """Consume whitespace and Lean line/nested-block comments."""
        consumed = False
        while self.i < len(self.text):
            if self.text[self.i].isspace():
                if self.text[self.i] == "\t":
                    self.error("tabs are not allowed")
                self.i += 1
                consumed = True
            elif self.text.startswith("--", self.i):
                newline = self.text.find("\n", self.i + 2)
                self.i = len(self.text) if newline < 0 else newline + 1
                consumed = True
            elif self.text.startswith("/-", self.i):
                # Lean's `/--` and `/-!` doc comments are tokens, not
                # whitespace.  They end the module header just like a first
                # declaration does.
                if self.text.startswith("/--", self.i) or self.text.startswith("/-!", self.i):
                    return consumed, True
                depth = 1
                self.i += 2
                consumed = True
                while depth:
                    if self.i >= len(self.text):
                        self.error("unterminated block comment")
                    if self.text.startswith("/-", self.i):
                        depth += 1
                        self.i += 2
                    elif self.text.startswith("-/", self.i):
                        depth -= 1
                        self.i += 2
                    else:
                        self.i += 1
            else:
                break
        return consumed, False

    def starts_word(self, word):
        if not self.text.startswith(word, self.i):
            return False
        end = self.i + len(word)
        return end == len(self.text) or not self.is_ident_char(self.text[end])

    @staticmethod
    def is_letter_like(char):
        """Lean 4.32.1's `Init.isLetterLike`, copied as ranges rather than guessed."""
        value = ord(char)
        return (
            0x3B1 <= value <= 0x3C9 and value != 0x3BB
        ) or (
            0x391 <= value <= 0x3A9 and value not in (0x3A0, 0x3A3)
        ) or (
            0x3CA <= value <= 0x3FB
        ) or (
            0x1F00 <= value <= 0x1FFE
        ) or (
            0x2100 <= value <= 0x214F
        ) or (
            0x1D49C <= value <= 0x1D59F
        ) or (
            0x00C0 <= value <= 0x00FF and value not in (0x00D7, 0x00F7)
        ) or 0x0100 <= value <= 0x017F

    @staticmethod
    def is_subscript_alnum(char):
        value = ord(char)
        return (
            0x2080 <= value <= 0x2089
            or 0x2090 <= value <= 0x209C
            or 0x1D62 <= value <= 0x1D6A
            or value == 0x2C7C
        )

    @classmethod
    def is_ident_first(cls, char):
        return char == "_" or char.isalpha() or cls.is_letter_like(char)

    @classmethod
    def is_ident_char(cls, char):
        """Lean 4.32.1's `isIdRest`."""
        return (
            char in "_'!?"
            or char.isalnum()
            or cls.is_letter_like(char)
            or cls.is_subscript_alnum(char)
        )

    def take_word(self, word):
        if not self.starts_word(word):
            return False
        self.i += len(word)
        return True

    def scan_string(self):
        """Only used when a string occurs where a header command must begin."""
        self.i += 1
        while self.i < len(self.text):
            if self.text[self.i] == '\"':
                self.i += 1
                return
            if self.text[self.i] == "\\\\":
                self.i += 2
            else:
                self.i += 1
        self.error("unterminated string literal")

    def scan_raw_string(self):
        """Recognize Lean's `r###"..."###` form at header scope."""
        start = self.i
        self.i += 1  # r
        hashes = 0
        while self.i < len(self.text) and self.text[self.i] == "#":
            hashes += 1
            self.i += 1
        if self.i >= len(self.text) or self.text[self.i] != '\"':
            self.i = start
            return False
        self.i += 1
        closer = '\"' + ("#" * hashes)
        end = self.text.find(closer, self.i)
        if end < 0:
            self.error("unterminated raw string literal")
        self.i = end + len(closer)
        return True

    def read_component(self):
        if self.i >= len(self.text):
            return None
        if self.text[self.i] == "«":
            end = self.text.find("»", self.i + 1)
            if end < 0:
                self.error("unterminated quoted identifier")
            component = self.text[self.i + 1:end]
            if not component:
                self.error("empty quoted identifier")
            self.i = end + 1
            return component
        if not self.is_ident_first(self.text[self.i]):
            return None
        start = self.i
        self.i += 1
        while self.i < len(self.text) and self.is_ident_char(self.text[self.i]):
            self.i += 1
        return self.text[start:self.i]

    def read_module_name(self):
        components = []
        component = self.read_component()
        if component is None:
            self.error("expected module identifier after import")
        components.append(component)
        while self.i < len(self.text) and self.text[self.i] == ".":
            self.i += 1
            if self.i >= len(self.text) or self.text[self.i].isspace():
                self.error("incomplete module identifier")
            component = self.read_component()
            if component is None:
                self.error("invalid module identifier")
            components.append(component)
        return tuple(components)

    @staticmethod
    def local_module(components):
        """Map Lean identifier components to this repository's module spelling."""
        if components == ("Blanc",) or components == ("Main",):
            return components[0]
        if len(components) >= 2 and components[0] == "Blanc":
            return ".".join(components[1:])
        return None

    def read_import(self):
        # The toolchain grammar is optional `public`, optional `meta`, `import`,
        # optional `all`, then `identWithPartialTrailingDot`, in exactly this order.
        saw_public = self.take_word("public")
        if saw_public:
            _, ends_header = self.skip_trivia()
            if ends_header:
                return False, None, False, False, False
        saw_meta = self.take_word("meta")
        if saw_meta:
            _, ends_header = self.skip_trivia()
            if ends_header:
                return False, None, False, False, False
        if not self.take_word("import"):
            # Once an import-only modifier has begun a header command, another
            # modifier cannot silently turn it into a body boundary.  In
            # particular Lean rejects `meta public import`; treating it as a
            # declaration would hide the later import from this gate.
            if (saw_public or saw_meta) and (
                self.take_word("public")
                or self.take_word("meta")
                or self.take_word("all")
            ):
                self.error("invalid import modifier order")
            return False, None, False, False, False
        had_trivia, ends_header = self.skip_trivia()
        if ends_header or not had_trivia:
            self.error("expected whitespace and a module identifier after import")
        saw_all = self.take_word("all")
        if saw_all:
            had_trivia, ends_header = self.skip_trivia()
            if ends_header or not had_trivia:
                self.error("expected whitespace and a module identifier after import all")
        return True, self.local_module(self.read_module_name()), saw_public, saw_meta, saw_all

    def imports(self):
        out = []
        saw_module = False
        while True:
            _, ends_header = self.skip_trivia()
            if ends_header:
                return out
            if self.i >= len(self.text):
                return out
            if self.text[self.i] == '"':
                # A literal at header scope cannot be an import.  Scan it only
                # to distinguish a valid body-shaped token from malformed state.
                self.scan_string()
                return out
            if self.text[self.i] == "r" and self.scan_raw_string():
                return out
            if not saw_module and self.take_word("module"):
                saw_module = True
                continue
            if self.take_word("prelude"):
                continue
            recognized, imported, saw_public, saw_meta, saw_all = self.read_import()
            if not recognized:
                # First declaration (or any other non-header command): Lean's
                # header parser has finished, so later text is deliberately out
                # of scope even if it resembles an import command.
                return out
            if (saw_public or saw_meta or saw_all) and not saw_module:
                self.error("public, meta, and all imports require a module header")
            if saw_public and saw_all:
                self.error("public import cannot be combined with all")
            if imported is not None:
                out.append(imported)


def imports_of(path):
    """Return local imports in the Lean module header, failing closed on bad trivia."""
    with open(path, encoding="utf-8") as handle:
        return [module for module in HeaderScanner(handle.read()).imports() if module]


# ---------------------------------------------------------------------------
# Check 5: discovery reachability of the shared stratum.
# ---------------------------------------------------------------------------

COMMON_API = os.path.join("docs", "COMMON_API.md")
PROOF_RECIPES = os.path.join("scripts", "proof-recipes.toml")

# A cited path looks like `Blanc/MemoryImage.lean` in backticks; the registry
# also links them, and a Markdown link's label is the backticked form, so one
# pattern covers both spellings.
CITED_MODULE = re.compile(r"`(Blanc/[A-Za-z0-9_/]+\.lean)`")


# Check 6 (tightened 2026-11-01): a citation counts toward discovery only when
# it sits inside the need-first tree -- the Root section or a need section
# (`## E — execution`, `## I — ...`, ..., `## C — ...`) -- and outside a fenced
# code block. A path mentioned only in the preamble, in the closing
# common-library-first workflow, or in an appended tail below every need
# branch is not reachable by following the branches, which is what the
# registry promises; one citation appended at the end of the file used to
# satisfy this check.
NEED_SECTION = re.compile(r"^## (?:Root\b|[A-Z] — )")


def branch_citations(api_text):
    """Cited module paths that lie inside the need-first tree."""
    cited = set()
    in_branch = False
    in_fence = False
    for line in api_text.splitlines():
        if line.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if line.startswith("## "):
            in_branch = bool(NEED_SECTION.match(line))
            continue
        if in_branch:
            cited.update(CITED_MODULE.findall(line))
    return cited


def module_name_of(relative_path):
    """`Blanc/Composition/X.lean` -> `Composition.X`, as the table spells it."""
    trimmed = relative_path[len("Blanc/"):-len(".lean")]
    return trimmed.replace("/", ".")


# ---------------------------------------------------------------------------
# Check 6: every SHARED module is reachable from the need-first registry.
#
# Keyed by module name as the classification table spells it. The value is the
# reason the module is not something an author could be told to find, and it is
# part of the gate: `shared_coverage_failures` rejects an exemption whose module
# is no longer shared, no longer on disk, or now cited, so the table prunes
# itself instead of silently absorbing the next shipped facility.
#
# "It is not documented yet" is not a reason and must not be added here. The
# only admissible reasons are the three shapes below: a module that declares
# nothing, the registry's own machinery, and a control fixture.
# ---------------------------------------------------------------------------

DISCOVERY_EXEMPT = {
    "ProofRecipeTactic": (
        "the need-first registry's own machinery: this is the authoring leaf that "
        "reads the generated recipes, deliberately unreachable from Blanc.lean, so "
        "citing it would point an author at the mechanism instead of a facility"
    ),
    "ProofRecipesGenerated": (
        "generated artifact: it is produced from scripts/proof-recipes.toml by "
        "scripts/generate-proof-recipes.py and carries no hand-authored API"
    ),
}


def shared_coverage_failures(owner, found, citations):
    """Shared modules the need-first registry cannot reach, and stale exemptions.

    Returns (failures, n_shared, n_shared_cited). The exemption table is
    validated in both directions so it cannot drift in either.
    """
    failures = []
    shared = sorted(m for m in found if owner.get(m) == "shared")
    cited = []
    for mod in shared:
        path = "Blanc/" + mod.replace(".", "/") + ".lean"
        if path in citations:
            cited.append(mod)
            if mod in DISCOVERY_EXEMPT:
                failures.append(
                    f"{mod} is exempted from the shared-discovery obligation "
                    f"({DISCOVERY_EXEMPT[mod]}) but {COMMON_API} now cites "
                    f"{path} — remove the DISCOVERY_EXEMPT row so check 6 covers it"
                )
            continue
        if mod in DISCOVERY_EXEMPT:
            continue
        failures.append(
            f"{path} is classified SHARED in scripts/check-layering.py but "
            f"{COMMON_API} never cites it inside the need-first tree (Root or a "
            f"need section, outside fenced code) — a module the repository calls "
            f"contract-neutral and reusable that the need-first registry cannot "
            f"reach; add a branch entry for it, or add a DISCOVERY_EXEMPT row "
            f"stating why it is not a facility an author could be told to find"
        )

    for mod, reason in sorted(DISCOVERY_EXEMPT.items()):
        if mod not in found:
            failures.append(
                f"DISCOVERY_EXEMPT lists {mod} ({reason}), but no such module "
                f"exists — the exemption table is stale"
            )
        elif owner.get(mod) != "shared":
            failures.append(
                f"DISCOVERY_EXEMPT lists {mod} ({reason}), which is classified "
                f"{owner.get(mod)!r} rather than shared — the exemption table is stale"
            )

    if not cited:
        failures.append(
            f"{COMMON_API} cites no shared module at all — check 6 would pass "
            f"over an empty population"
        )
    return (failures, len(shared), len(cited))


def discovery_failures(root, owner):
    """Missing and stale discovery entries for the shared stratum.

    Returns (failures, n_shared_recipes, n_citations). Absent or unreadable
    inputs are failures, not skips.
    """
    failures = []
    api_path = os.path.join(root, COMMON_API)
    registry_path = os.path.join(root, PROOF_RECIPES)

    try:
        with open(api_path, encoding="utf-8") as handle:
            api_text = handle.read()
    except OSError as exc:
        return ([f"cannot read the need-first registry {COMMON_API}: {exc}"], 0, 0)

    try:
        with open(registry_path, "rb") as handle:
            registry = tomllib.load(handle)
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return ([f"cannot read the proof-recipe registry {PROOF_RECIPES}: {exc}"], 0, 0)

    citations = set(CITED_MODULE.findall(api_text))
    reachable = branch_citations(api_text)
    for cited in sorted(citations):
        if not os.path.isfile(os.path.join(root, cited)):
            failures.append(
                f"{COMMON_API} cites {cited}, which does not exist — the "
                f"registry entry is stale"
            )

    shared_owned = []
    for index, recipe in enumerate(registry.get("recipe", [])):
        if not isinstance(recipe, dict) or recipe.get("status") != "active":
            continue
        owner_module = recipe.get("owner_module")
        recipe_id = recipe.get("id", f"recipe[{index}]")
        if not isinstance(owner_module, str) or not owner_module.startswith("Blanc/"):
            failures.append(
                f"{PROOF_RECIPES}: active recipe {recipe_id!r} has no usable "
                f"owner_module — cannot judge its discoverability"
            )
            continue
        if owner.get(module_name_of(owner_module)) != "shared":
            continue
        shared_owned.append(recipe_id)
        if owner_module not in reachable:
            failures.append(
                f"{owner_module} is a shared facility owned by active proof "
                f"recipe {recipe_id!r} but {COMMON_API} never cites it inside "
                f"the need-first tree (Root or a need section) — a reusable "
                f"facility that the need-first registry cannot reach"
            )

    if not citations:
        failures.append(
            f"{COMMON_API} cites no Blanc module at all — the need-first "
            f"registry has been reworded out of this check's sight"
        )
    if not shared_owned:
        failures.append(
            f"{PROOF_RECIPES} has no active recipe owned by a shared module — "
            f"check 5 would pass over an empty population"
        )
    return (failures, len(shared_owned), len(citations))


INVENTORY_DOC = os.path.join("docs", "MODULE_INVENTORY.md")


def load_inventory_generator():
    """scripts/generate-module-inventory.py, loaded beside this script."""
    import importlib.util

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "generate-module-inventory.py")
    spec = importlib.util.spec_from_file_location("module_inventory", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"REGRESSION — layering: cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def architecture_failures(root, owner, found, compositions):
    """Pure source audit shared by the gate and disposable minimal controls.

    `owner` and `compositions` come from validated classification. No discovery
    surface or Lean elaboration is needed to exercise this import relation.
    """
    failures = []

    for mod in sorted(set(found) - set(owner)):
        failures.append(
            f"{mod} is not classified in scripts/check-layering.py — add it to "
            f"SHARED, a CONTRACTS entry, COMPOSITION, or ROOTS"
        )

    for mod in sorted(set(owner) - set(found)):
        failures.append(
            f"{mod} is classified in scripts/check-layering.py but no such module "
            f"exists — the table is stale"
        )

    for mod in sorted(found):
        category = owner.get(mod)
        if category is None or category == "root":
            continue
        try:
            imports = imports_of(found[mod])
        except HeaderParseError as exc:
            relative = os.path.relpath(found[mod], root)
            failures.append(f"{relative}: cannot determine module header imports: {exc}")
            continue
        for imported in imports:
            target = owner.get(imported)
            if target is None:
                continue
            if target == "root":
                # Roots aggregate; nothing in the graph depends back on them.
                # Only composition is checked here, because a shared or
                # contract module importing a root is already an import cycle
                # the toolchain rejects, while composition is the new category
                # whose one-way relation to the roots this gate must state.
                if category == "composition":
                    failures.append(
                        f"{mod} (composition) imports Blanc.{imported}, a root "
                        f"module — roots aggregate composition, not the reverse"
                    )
                continue
            if target == "composition":
                if category != "composition":
                    failures.append(
                        f"{mod} ({category}) imports Blanc.{imported}, a composition "
                        f"module — the composition stratum is downstream of the "
                        f"shared and contract layers"
                    )
                else:
                    excess = set(compositions[imported]) - set(compositions[mod])
                    if excess:
                        failures.append(
                            f"{mod} (composition) imports Blanc.{imported}, a composition "
                            f"with undeclared family/families {', '.join(sorted(excess))} "
                            f"— imported composition families must be a subset of "
                            f"{', '.join(compositions[mod])}"
                        )
                continue
            if target == "shared":
                continue
            if category == "shared":
                failures.append(
                    f"{mod} (shared) imports Blanc.{imported}, a {target} module — "
                    f"a shared layer must not depend on a contract"
                )
            elif category == "composition":
                if target not in compositions[mod]:
                    failures.append(
                        f"{mod} (composition) imports Blanc.{imported}, owned by "
                        f"undeclared family {target} — declared families: "
                        f"{', '.join(compositions[mod])}"
                    )
            elif target != category:
                failures.append(
                    f"{mod} ({category}) imports Blanc.{imported}, owned by {target} "
                    f"— contracts are siblings; factor the shared part upstream"
                )

    return failures


def main(argv):
    root = None
    args = list(argv[1:])
    while args:
        arg = args.pop(0)
        if arg == "--root":
            if not args:
                raise SystemExit("REGRESSION — layering: --root needs a directory")
            root = args.pop(0)
        else:
            raise SystemExit(f"REGRESSION — layering: unknown argument {arg!r}")
    if root is None:
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

    owner = classify()
    found = modules_on_disk(root)
    if not found:
        raise SystemExit(f"REGRESSION — layering: no Lean modules found under {root}")

    failures = architecture_failures(root, owner, found, COMPOSITION)

    discovery, n_shared_recipes, n_citations = discovery_failures(root, owner)
    failures.extend(discovery)

    api_path = os.path.join(root, COMMON_API)
    try:
        with open(api_path, encoding="utf-8") as handle:
            citations = branch_citations(handle.read())
    except OSError as exc:
        failures.append(f"cannot read the need-first registry {COMMON_API}: {exc}")
        citations = set()
    coverage, n_shared, n_shared_cited = shared_coverage_failures(
        owner, found, citations
    )
    failures.extend(coverage)

    # Check 7: the generated shared-module inventory matches its generator,
    # which renders it from this table, the modules' own headers and the
    # registry's need-tree citations (scripts/generate-module-inventory.py).
    inventory = load_inventory_generator()
    failures.extend(inventory.check(root, sys.modules[__name__], owner))

    for line in failures:
        print(f"LAYERING — {line}")
    n_checked = sum(1 for m in found if owner.get(m) not in (None, "root"))
    if failures:
        print(
            f"REGRESSION — layering: {len(failures)} violation(s) across "
            f"{len(CONTRACTS)} contract(s), {len(found)} module(s)"
        )
        return 1
    n_composition = sum(1 for m in found if owner.get(m) == "composition")
    print(
        f"OK — layering: {len(CONTRACTS)} contract(s) are siblings; "
        f"{len(found)} module(s) classified, {n_checked} non-root checked, "
        f"{n_composition} composition module(s) downstream, "
        f"no cross-contract, inverted or undeclared-family composition import; "
        f"{n_shared_recipes} shared facility recipe(s) reachable from "
        f"{n_citations} need-first registry citation(s), none stale; "
        f"{n_shared_cited}/{n_shared} shared module(s) cited by the need-first "
        f"registry, {len(DISCOVERY_EXEMPT)} exempt with a stated reason; "
        f"{INVENTORY_DOC} matches its generator"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
