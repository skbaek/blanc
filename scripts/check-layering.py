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

SHARED = ["Basic", "BytePattern", "Semantics", "HistoricalFork", "ShanghaiOnwards", "CommonCore", "MachineDataFacts", "RlpConcrete", "RlpListEncode", "RlpBytesInjective", "RlpRoundTrip",
          "ProofRecipesGenerated", "ProofRecipeTactic", "Tactics", "CommonProofs.Base", "CommonProofs.Frames", "CommonProofs.MemImage", "CommonProofs.Messages", "CommonProofs.Walk", "CommonProofs.Hinv", "CommonProofs.NoDel", "CommonProofs.Balance", "Ladder", "BalanceAlgebra", "LedgerConservation", "StorageOnlySpec", "SlotFootprint", "FakeExponential", "FakeExponentialGrowth", "FakeExponentialEval", "WordFakeExponential", "WordFakeExponentialBound", "WordFakeExponentialEval", "FakeExponentialWordCorrespondence", "FakeExponentialWordDomain", "WordArithmetic", "WordByteCodecs", "WordByteRoundtrip", "MemoryImage", "BytesWrite", "MemoryLayout", "MemoryStageGas",
          "Compiled", "DeploymentMessage", "DeploymentTouch", "Forward", "ForwardFlatAccess",
          "Reverts", "ForwardCall", "ForwardStorageAccess", "StorageAccessGas", "StorageRefund", "ForwardSha256",
          "StaticPrecompileMessage", "StaticStorage", "TerminalStorage",
          "CompiledStackSafety", "AbstractStackSafety",
          "AbstractStackTransfer", "CodeTrie", "GasErasure", "RunPrefix", "PrefixTransport",
          "RevertPayload", "CompiledWalkInversion", "CompiledFixedInvariance", "ExecDeterminism", "ExecIdentification", "ExecutionSettlement", "ExecutionPath",
          "ExecutionStateTrace", "ExecutionTrace", "ExecutionStagedBodyTrace", "ExecutionStagedBodyStateTrace", "RequestsOutput", "ExecutionMessageStateTrace",
          "ExecutionTransactionStateTrace", "ExecutionSelectedTransactionStateTrace", "ExecutionTransactionGas", "ExecutionBodyGas", "ExecutionBodyStateTrace", "ExecutionHistory", "JointHistory", "ConsensusSsz", "ExecutionHistoryExtension",
          "ExecutionHistoryStateTrace", "ExecutionHistoryInStateTrace", "ExecutionOccurrence", "ExecutionNoninterference", "TransientSettlement", "TransientInvariance", "ExecutionCreateGuard",
                                 "ExecutionDeletionProvenance",
                                 "ExecutionEmptyContext",
                                 "ExecutionNonceKeep",
                                 "ExecutionHistoryInSystemEnvironment",
                                 "ExecutionHistoryInSystemOpenings",
                                 "ExecutionMidHistoryCallers",
                                 "ExecutionMidHistoryInCallerExclusion",
                                 "ExecutionNonceCode",
                                 "ExecutionRetainedCodeSettlement",
                                 "Lift.CreateSettlementMeta",
                                 ]
SHARED += ["JointTime", "Lift.StaticcallCapability"]
# Newly extracted common modules live in a separate additive row so concurrent
# contract branches can extend the historical table cleanly.
SHARED += ["MessageExecution", "MessageExecutionInversion",
           "LogBloom", 
           "ExecutionSenderOccurrences", "ExecutionSenderRootCallers", 
           "AddressSlot", "AddressSlotProofs", "MessageResult",
           "DelegatecallEnvelope",
           "ExecutionFrames", "ExecutionCommittedGas", "ExecutionMessageGas", "ExecutionFrameEntry", "ExecutionCallerExclusion", "ExecutionTraceCallerExclusion", "ExecutionFrameTime", "ExecutionHistoryFrameTime", "ExecutionAdmission", "ContractAdmission",
           "ExecutionMessageAdmission", "ExecutionTransactionAdmission",
           "ExecutionTransactionPrefix", "ExecutionTransactionPrefixAdmission",
           "ExecutionBodyAdmission", "ExecutionBodyPrefixAdmission", "ExecutionHistoryAdmission",
           "ExecutionTraceFresh", "ExecutionTraceEntered", "ExecutionImmutableCode",
           "ExecutionMessageEffects", "ExecutionTransactionEffects", "ExecutionParentLogAttribution", "ExecutionSettledReceiptLogs",
           "ExecutionBodyEffects", "ExecutionRewardCredits", "ExecutionHistoryEffects",
           "ExecutionAccountingReplay", "ExecutionAccountingSignedBalance", "ExecutionAccountingStorageFold",
           "ExecutionAccountingStoragePrefix",
           "ExecutionAccountingLadder", "CallSpawnExact", "StaticcallObservation", "StaticCallStorage",
           "ChargeGas", "ExecutionTraceFrames", "ExecutionTraceAdmission", "ExecutionTraceSettledFrames", "ExecutionTraceSettledOrigin", "ExecutionStagedFrames", "ExecutionStagedAdmission", "ExecutionStagedFrameEnv", "ExecutionStagedRootFacts", "ExecutionStagedSstoreAttribution", "ExecutionTraceRootFrame", "ExecutionRequestSegments", "ExecutionTraceEntry", "ExecutionExistingAccount", "ExecutionDeletionSafety", "ExecutionRetainedDeletionSafety", "ExecutionNoDelProducer", "ExecutionNoDelSafeHistory", "ExecutionRetainedNoDelTransaction", "ExecutionRetainedNoDelHistory", "ExecutionTraceDeterminism", "ExecutionNoDelTransaction", "ExecutionNoDelHistory", "ExecutionHistoricalAdmission", "ExecutionHistoricalLadder",
           "ExecutionAccountingObserved", "ExecutionAccountingAdmission", "ExecutionAccountingCore", "ExecutionEntryAccounting", "ExecutionModelAccounting", "ExecutionWholeFrameAccounting", "ExecutionDirectCode", "ExecutionAccountingStepsIn", "ExecutionAccountingCoreIn", "ExecutionAccountingAdmissionIn", "ExecutionAccountingHistoryIn"]
# The ladder over arbitrary code images and the generic bytecode lift
# (solc-bytecode-v1): contract-neutral, no WETH9 name in any of them.
SHARED += ["LadderBase", "LadderReached", "MessageDelegationGas", "LadderSem", "ContractAdmissionSem", "ExecutionAdmissionSem",
           "Lift.Basic", "Lift.Check", "Lift.CallEffects", "Lift.Transfer", "Lift.Sound", "Lift.Exact",
           "Lift.ExactWalk", "Lift.Silent", "Lift.BalSilent"]
# Loops, kernel-economical checking, walk kits and solc idioms (beacon-deposit-bytecode-v1):
# contract-neutral, no contract name in any of them.
SHARED += ["Lift.Loop", "Lift.CheckFast", "Lift.ExactWalkOps",
           "Lift.ExactWalkCut", "Lift.ExactWalkCutOps", "Lift.CopyLoop", "Lift.PackedSha",
           "Lift.PackedShaCovered", "Lift.Quiet", "Lift.InvWalk", "Lift.InvWalkOps",
           "Lift.InvWalkWorld", "Lift.InvWalkGas", "Lift.ExactMustRun", "Lift.InvWalkSha", "Lift.InvWalkDispatch", "Lift.InvWalkProvenance", "Lift.CodeSizeWalk", "Lift.HistAccessWalk", "Lift.HistStaticCall", "Lift.HistCursorCuts", "Lift.HistCursorReturn", "Lift.HistEcrecover", "Lift.HistCreate", "Lift.HistAccessMeta", "Lift.HistAccessWalkFacts"]
# Creation code (deploy-init-v1): the size-optimised packed-hash site and the CREATE bridge
# for lifted creation code; contract-neutral.
SHARED += ["RequestFeeWord", "RequestFeeWordDomain", "RequestFeeWordBound", "Lift.RequestFee.Window", "Lift.RequestFee.Getter"]
# The plain (EIP-7002/EIP-7251) user path over the shared fee window (blanc-eip7251-consolidation-requests-v1).
SHARED += ["Lift.RequestFee.Plain"]
SHARED += ["Lift.Deploy", "Lift.CreationOps", "Lift.Create2Deploy", "Lift.CreateEntry", "Lift.Clone1167", "Lift.CheckRange"]
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
           "Lift.WriteSiteSound", "Lift.WriteSiteZero",
           "Lift.WriteSiteReach", "Lift.WriteSiteReachHistory", "Lift.ReachWalkSstore"]
# The shared symbol-interval reading of the bound checkers (ns-h1b): imports
# nothing but core Lean, so it is contract-neutral.
SHARED += ["Lift.BndInterval", "Lift.ReturnDataKeep"]
# Generic list positions in a flatMap (EIP-7002 cross-layer P2); imports nothing.
SHARED += ["ListFlatMapPosition"]
# Fixed-width list chunks, a list's one marked element, and the element at a flatMap position
# (eip8282-gloas-cross-layer-v1 R1); imports nothing.
SHARED += ["ListChunks"]
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
           ]
# Fuel-bounded loop heads (Newton loops) walked to a fuel-loop model: contract-neutral.
SHARED += ["Lift.FuelLoopWalk"]
# Vyper 0.2.x walk kit (array slots, identity copies, raw_call tails, balance differences):
# contract-neutral.
SHARED += ["Lift.VyperArraySlot", "Lift.IdentityCall", "Lift.BalanceDiffCall",
           "Lift.VyperRawCall", "Lift.RunEx", "Lift.WalkKit", "Lift.WalkInvKit", "Lift.FrameWalkAligned"]
# Internal calls through the PC idiom and unrolled Vyper frame save/restore chains: contract-neutral.
SHARED += ["Lift.VyperFrameLoop"]
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
SHARED += ["Lift.StaticCall", "Lift.StaticCallGuard", "Lift.WalkSteps", "Lift.MapSlot", "Lift.Vyper", "Lift.PackedWord"]
# Spawn kinds from code bytes (curve-3pool-stableswap-v1): contract-neutral.
SHARED += ["Lift.SpawnKindsM"]
SHARED += ["Lift.GuardedCalls"]
SHARED += []
SHARED += []
SHARED += []
# The frame cursor, the reentrancy-lock exclusion kit and its bytecode checker, owner
# discipline, and concrete-run evaluation (deployed-lido-vyper-v1): contract-neutral.
SHARED += ["Lift.Reach", "Lift.ReachWalk", "Lift.ReachChain", "Lift.ReachDispatch", "Lift.Cursor", "Lift.CursorCuts", "Lift.ObservedReach", "Lift.CursorKeccak", "Lift.CursorKeccakOrder", "Lift.CursorOccurrence", "Lift.CursorCutsToward", "Lift.CursorStateToward", "Lift.CursorTreeNinst", "Lift.CursorExact", "Lift.CursorExactLine", "Lift.CallRestriction", "Lift.StaticOnlyFrames", "LockExclusion", "OwnerDiscipline", "ConcreteRun",
           "Lift.LockCheck", "Lift.LockCheckSound", "Lift.LockCheckFlow", "Lift.CursorStateCuts", "Lift.CursorNoExecSuffix", "Lift.CursorSourceRun", "Lift.CursorSourceRunReturn", "Lift.CursorBalanceReply", "Lift.CursorQuietReturn", "Lift.CursorJump"]
# The constant memory map and its checker, code tries as data, and the executable-witness
# engine with its child runs and spawn facts (deployed-lido-vyper-v1, V-): contract-neutral.
SHARED += ["Lift.MemMap", "Lift.CheckMem", "Lift.CodeTriesData", "Lift.CodeTriesBuild", "Lift.WitnessArms", "Lift.Witness",
           "Lift.WitnessChild", "Lift.WitnessSpawn", "Lift.NodeWalk", "Lift.KernelBatch"]
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
SHARED += ["ExecutionTraceCalldata", "ForkUniform", "Lift.NodeWalkFork", "Lift.WitnessFork", "Lift.NodeWalkOrig"]
# A gas-exact lifted run as a node-walk leaf child (vyper-reachable-reentrancy-v1).
SHARED += ["Lift.ExactLeaf"]
# A forall kernel batch (vyper-minus-reachable-reentrancy-v1).
SHARED += ["Lift.KernelBatchForall", "Lift.ShadowTail"]
# Generic entry-gas bound, child code-at keep and system-size exclusion of a configured history
# (curve-3pool-stableswap-v1 packet G): contract-neutral.
SHARED += ["ExecutionTraceFrameEnv"]

SHARED += ["Lift.GasErasureRun", "Lift.MutableCallPost"]


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
    "ExecutionInCodeImage",
    "ExecutionInOwnCode",
    "ExecutionInCodeImageSafe",
    "ExecutionInRawNodes",
    "ExecutionCellProvenance",
    "ExecutionKeptFrames",
    "ExecutionKeptFacts",
    "ExecutionKeptTop",
    "ExecutionKeptChain",
    # Covered configured histories as kept histories, the splice, and the kept carrier's uniqueness
    # (eip8282-gloas-cross-layer-v1 R13).
    "ExecutionKeptConfigured",
    # Gloas joint runs over jointStepG and the joint-level invariants G3-09..11 (eip8282-gloas-cross-layer-v1 RUN).
    "JointGloasHistory",
    "JointGloasInvariants",
    "ExecutionKeptValue",
    "ExecutionInCellProvenance",
    "ExecutionCommittedCell",
    "ExecutionSettledRootEntry",
    "ExecutionHistoryCommittedCell",
    "ExecutionHistoryInEraBounds",
    "ExecutionHistoryCommittedCuts",
    "ExecutionTrieBinding",
    "ExecutionHistoryCellProvenance",
    "ExecutionInRawNodeOrigin",
    "ExecutionInRootOwnCode",
    "ExecutionHistoryCellProvenanceFrom",
    "Lift.DelegatecallControl",
    "Lift.FrameSkip",
    "Lift.InvWalkStep",
    "Lift.ReachSkip",
    "Lift.RunPWalk",
    "Lift.SolcStorageClear",
    "Lift.SolcStoragePayload",
    "Lift.SolcStringAllocation",
    "Lift.SolcAbiStringStaging",
    "Lift.SolcStorageReturn",
    "Lift.ReachSstoreLoops",
    "Lift.ReachSolcStringStore",
    "Lift.SelectorRoute", "Lift.ShuffleSkip",
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
                           "Lift.WithdrawalRequest.HistoryFifo", "Lift.WithdrawalRequest.BoundaryFifo",
                           "Lift.WithdrawalRequest.JointHistory",
                           "Lift.WithdrawalRequest.RequestCodec", "Lift.WithdrawalRequest.JointLatency",
                           "Lift.WithdrawalRequest.LatencyControl",
                           "Lift.WithdrawalRequest.AnchorInvControl",
                           "Lift.WithdrawalRequest.JointAuthorization",
                           "Lift.WithdrawalRequest.JointFate",
                           "Lift.WithdrawalRequest.IgnoreWitnesses",
                           "Lift.WithdrawalRequest.OrderWitness",
                           "Lift.WithdrawalRequest.JointCrediting",
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
}

# Frozen byte producer and its conditional original-cut consumer.
SHARED += ["ExecutionBodyTransactionCut"]
SHARED += ["Lift.LegacyRecover"]

# Finite hash separation, the kernel trie-root twin with its node-hash certificate, and header
# binding (weth9-observation-binding-v1): contract-neutral.
SHARED += ["Separated", "TrieKernel"]







SHARED += ["Lift.AccumulatedWalk", "Lift.GasField"]
SHARED += ["SyntheticSystemWorld", "SyntheticBpo2Envelope"]


SHARED += []

SHARED += ["Lift.CallMessageFacts"]

SHARED += ["ExecutionTargetPrefix"]

# Fixed synthetic 299-byte token fixture, shared without V± instance worlds.
SHARED += ['Lift.Token20.Cert', 'Lift.Token20.Check', 'Lift.Token20.Creation.Cert', 'Lift.Token20.Creation.Check', 'Lift.Token20.Creation.Input', 'Lift.Token20.Run', 'Lift.Token20.RunBalance']

# Execution facts over selected-domain histories, transaction-item transport and the block-hash
# binding, and the frame-chain, coin-frame, root-standing, write-site and walk-cost kits
# (curve-3pool-flagship-v1): contract-neutral. `Lift.CodeImage` keeps a pinned `Lift.Usdc`
# constant name, moved here because a shared kit needs it; the definition names no contract.
SHARED += [
    "ExecutionHistoryInFrameEnv",
    "ExecutionMidHistoryInOwnCode",
    "ExecutionReceiptLogLink",
    "Lift.BalanceLocality",
    "Lift.CodeImage",
    "Lift.ForeignKeep",
    "Lift.FrameChain",
    "Lift.HistIdentityCall",
    "Lift.InvWalkLegacy",
    "Lift.LinearRuntimeSafety",
    "Lift.ReachKinds",
    "Lift.RootChain",
    "Lift.RootStanding",
    "Lift.ViewChain",
    "Lift.WalkCost",
    "Lift.WalkCostExact",
    "Lift.WriteSiteMapping",
]

# EIP-8282 builder request contracts (deposit and exit): the lifted runtimes and init codes, their
# registered certificates, and the deployment through the shared CREATE2 factory walk. One family
# for the two contracts; it never imports another contract family, and the generic factory and
# runtime-install steps it uses are the shared modules registered just below.
SHARED += ["Lift.Create2Factory.Cert", "Lift.Create2Factory.Check", "Lift.Create2Factory.Code",
           "Lift.Create2Factory.Jumps", "Lift.Create2Factory.Walk", "Lift.RuntimeInstall"]
# Amsterdam walk-engine support (blanc-eip8282-builder-requests-v1 O6): the state-gas `SSTORE` and
# `SLOAD` steps and the top-level system-call envelope, contract-neutral. `CoveredFork` is not widened.
SHARED += ["Lift.AmsterdamWalk", "Lift.ExecCut", "Lift.TransactionAmsterdam", "Lift.BalEffect",
    "Lift.AmsterdamAccess", "Lift.SystemCallAmsterdam"]
# The two pushed-word facts of a request contract's dispatch and inhibitor guard.
SHARED += ["Lift.SystemCaller", "MemoryWindows"]
# The system path all four Amsterdam request contracts share (blanc-eip8282-builder-requests-v1 O9).
SHARED += ["Lift.RequestSystem.Dispatch", "Lift.RequestSystem.Path", "Lift.RequestSystem.Call",
           "Lift.RequestSystem.Storage",
           "Lift.RequestSystem.Output", "Lift.RequestSystem.BodySegs", "Lift.RequestSystem.Access",
           "Lift.RequestSystem.PlainExcess", "Lift.SystemExecution.ConsolidationRequest.AmsterdamSystem",
           "Lift.RequestSystem.Effects"]
# The same system path on the covered forks (blanc-eip7251-consolidation-requests-v1 U2): a fork's stores
# (`SysStores`, with its Amsterdam and covered instances) and the covered forks' system-call envelope.
SHARED += ["Lift.RequestSystem.Stores", "Lift.RequestSystem.CoveredCall"]
# EIP-7251 consolidation requests (blanc-eip7251-consolidation-requests-v1): the covered-fork system call.
# It imports only shared modules; the lifted runtime and its fork-free system path are the shared
# `Lift.SystemExecution.ConsolidationRequest.*` modules registered above.
CONTRACTS.setdefault("consolidation-request", []).extend(["Lift.ConsolidationRequest.System"])
# The request queue model and the sequence statements, shared by the plain family (EIP-7251) and the EIP-8282
# builder family (blanc-eip7251-consolidation-requests-v1 U3): the drain for any excess arm, the queue model over
# effects, generic `Step`/`Chain` delivery, and the queue layout (`QueueLayout`, generic in record width,
# reclassified from the builder family).
SHARED += ["Lift.RequestQueue.Drain", "Lift.RequestQueue.Model", "Lift.RequestQueue.Chain",
           "Lift.BuilderRequest.QueueLayout"]
CONTRACTS.setdefault("consolidation-request", []).extend(["Lift.ConsolidationRequest.Queue",
                                                         "Lift.ConsolidationRequest.Delivery"])
# The covered-fork chain link over `RequestQueue.Step` (blanc-eip7251-consolidation-requests-v1 U4): a kept
# history's frames at a canonical request contract as a chain of steps; the EIP-7251 instance and its history.
SHARED += ["Lift.RequestQueue.Link"]
CONTRACTS.setdefault("consolidation-request", []).extend(["Lift.ConsolidationRequest.Chain"])
# The system path inverted (blanc-eip7251-consolidation-requests-v1 U5c): every successful system-arm run of a
# request runtime ends in `sysState` and returns the drained records; the EIP-7251 record body's inversion.
# `HistoryClean`, the per-block SYSTEM_ADDRESS premises, hoisted from the builder family's public observers.
SHARED += ["Lift.RequestSystem.PathInv", "Lift.RequestSystem.PrivilegedInv", "ExecutionKeptClean"]
CONTRACTS.setdefault("consolidation-request", []).extend(["Lift.ConsolidationRequest.SystemFrame"])
# Protocol-contract corpus G2 shared hoists: balance-silent kept-value bridge, kept-history pre-execution
# system-call connections, generic request-queue occurrence/latency laws, and joint-run ring/feed helpers.
SHARED += ["ExecutionKeptBalSilent", "ExecutionKeptPreCalls", "Lift.RequestQueue.Occurrence", "JointFeed"]
CONTRACTS["builder-request"] = [
    "Lift.BuilderRequest.Deposit.Code", "Lift.BuilderRequest.Deposit.Cert",
    "Lift.BuilderRequest.Deposit.Check", "Lift.BuilderRequest.Deposit.Jumps",
    "Lift.BuilderRequest.Deposit.Creation.Input", "Lift.BuilderRequest.Deposit.Creation.Cert",
    "Lift.BuilderRequest.Deposit.Creation.Check", "Lift.BuilderRequest.Deposit.Creation.Address",
    "Lift.BuilderRequest.Deposit.Creation.Deploy", "Lift.BuilderRequest.Deposit.FeeWindow",
    "Lift.BuilderRequest.Deposit.Submission", "Lift.BuilderRequest.Deposit.Frames",
    "Lift.BuilderRequest.FeePath",
    "Lift.BuilderRequest.Message", "Lift.BuilderRequest.Revert", "Lift.BuilderRequest.Transaction",
    "Lift.BuilderRequest.Deposit.Transaction", "Lift.BuilderRequest.Exit.Transaction",
    "Lift.BuilderRequest.TransactionWitness",
    "Lift.BuilderRequest.Deposit.Message", "Lift.BuilderRequest.Deposit.Revert",
    "Lift.BuilderRequest.Exit.Message", "Lift.BuilderRequest.Exit.Revert",
    "Lift.BuilderRequest.SystemPath", "Lift.BuilderRequest.SystemOutput",
    "Lift.BuilderRequest.Deposit.Fifo", "Lift.BuilderRequest.Exit.Fifo",
    "Lift.BuilderRequest.Latch", "Lift.BuilderRequest.Deposit.Latch",
    "Lift.BuilderRequest.Exit.Latch", "Lift.BuilderRequest.Deposit.Backlog",
    "Lift.BuilderRequest.ChainLink", "Lift.BuilderRequest.Deposit.ChainLink",
    "Lift.BuilderRequest.Exit.ChainLink",
    "Lift.BuilderRequest.Balances", "Lift.BuilderRequest.UserFrame",
    "Lift.BuilderRequest.Exit.Submission", "Lift.BuilderRequest.Exit.SubmissionAmsterdam",
    "Lift.BuilderRequest.Deposit.SubmissionAmsterdam",
    "Lift.BuilderRequest.UserFrameAmsterdam",
    "Lift.BuilderRequest.PrivilegedFrame",
    "Lift.BuilderRequest.Deposit.System", "Lift.BuilderRequest.Deposit.SystemCall",
    "Lift.BuilderRequest.Exit.System", "Lift.BuilderRequest.Exit.SystemCall",
    "Lift.BuilderRequest.Exit.Frames", "Lift.BuilderRequest.SystemFrame",
    "Lift.BuilderRequest.Exit.Code", "Lift.BuilderRequest.Exit.Cert",
    "Lift.BuilderRequest.Exit.Check", "Lift.BuilderRequest.Exit.Jumps",
    "Lift.BuilderRequest.Exit.Creation.Input", "Lift.BuilderRequest.Exit.Creation.Cert",
    "Lift.BuilderRequest.Exit.Creation.Check", "Lift.BuilderRequest.Exit.Creation.Address",
    "Lift.BuilderRequest.Exit.Creation.Deploy",
    "Lift.BuilderRequest.Delivery", "Lift.BuilderRequest.Deposit.Delivery",
    "Lift.BuilderRequest.Deposit.DeliveryWitness", "Lift.BuilderRequest.Exit.Delivery",
    "Lift.BuilderRequest.Exit.DeliveryWitness",
    "Lift.BuilderRequest.FeeDomain", "Lift.BuilderRequest.FeeRead", "Lift.BuilderRequest.FeeDomainWitness",
    "Lift.BuilderRequest.Deposit.FeeDomain", "Lift.BuilderRequest.Exit.FeeDomain",
    "Lift.BuilderRequest.Static", "Lift.BuilderRequest.Deposit.Static", "Lift.BuilderRequest.Exit.Static",
    "Lift.BuilderRequest.Flood", "Lift.BuilderRequest.Exit.Flood", "Lift.BuilderRequest.Surplus",
    "Lift.BuilderRequest.ValueKept",
    "Lift.BuilderRequest.Deposit.Properties", "Lift.BuilderRequest.Exit.Properties",
    "Lift.BuilderRequest.LoadBound", "Lift.BuilderRequest.Accepts",
    "Lift.BuilderRequest.WordFees",
    "Lift.BuilderRequest.RevertCovered", "Lift.BuilderRequest.Progress",
    "Lift.BuilderRequest.CallerCovered",
]
# EIP-8282 cross-layer R1 (eip8282-gloas-cross-layer-v1): occurrence-indexed submissions, emissions and queues over
# `KeptHistory`, generic over a linked builder contract, and its deposit and exit instances.
CONTRACTS["builder-request"].extend(["Lift.BuilderRequest.Occurrence", "Lift.BuilderRequest.Deposit.Indexed",
                                     "Lift.BuilderRequest.Exit.Indexed"])
# EIP-8282 cross-layer R13: the occurrence-indexed results across a covered (pre-Gloas) prefix.
CONTRACTS["builder-request"].extend(["Lift.BuilderRequest.Carrier"])
# EIP-8282 cross-layer RBA: the Gloas builder requests' serializations as the contracts' emitted records.
CONTRACTS["builder-request"].extend(["Lift.BuilderRequest.RequestCodecG", "Lift.BuilderRequest.RequestCodecGAmount"])
# EIP-7251 consolidation requests: fee and user frames under covered forks.
CONTRACTS.setdefault("consolidation-request", []).extend([
    "Lift.ConsolidationRequest.Fee", "Lift.ConsolidationRequest.Submission",
    "Lift.ConsolidationRequest.Frames",
])

# Beacon deposit contract, the deployed bytes (protocol-contract-corpus-v1, restored from the archive
# tag corpus-v1-20261105): the lifted runtime and creation code, the model and reference root it
# refines, and the frame, history and deployment-rooted results.
CONTRACTS["beacon-deposit"] = [
    "BeaconDepositCore", "BeaconDepositCorrectness", "BeaconDepositEncoding", "BeaconDepositModel",
    "Lift.BeaconDeposit.BeaconEnv", "Lift.BeaconDeposit.Body", "Lift.BeaconDeposit.BodyCount",
    "Lift.BeaconDeposit.BodyEvent", "Lift.BeaconDeposit.BodyEventHead", "Lift.BeaconDeposit.BodyEventKit",
    "Lift.BeaconDeposit.BodyEventLoop", "Lift.BeaconDeposit.BodyEventSig", "Lift.BeaconDeposit.BodyGuards",
    "Lift.BeaconDeposit.BodyInsertDead", "Lift.BeaconDeposit.BodyInsertLive", "Lift.BeaconDeposit.BodyNode",
    "Lift.BeaconDeposit.BodyPubkeyRoot", "Lift.BeaconDeposit.BodyShaKit",
    "Lift.BeaconDeposit.BodySignatureRoot", "Lift.BeaconDeposit.BodySpec", "Lift.BeaconDeposit.Cert",
    "Lift.BeaconDeposit.Check", "Lift.BeaconDeposit.CheckTries", "Lift.BeaconDeposit.CommittedExec",
    "Lift.BeaconDeposit.CommittedHistory", "Lift.BeaconDeposit.CommittedReplay",
    "Lift.BeaconDeposit.CountView", "Lift.BeaconDeposit.Creation.Cert", "Lift.BeaconDeposit.Creation.Check",
    "Lift.BeaconDeposit.Creation.Deploy", "Lift.BeaconDeposit.Creation.HistoricalDeploy",
    "Lift.BeaconDeposit.Creation.HistoricalTxInput", "Lift.BeaconDeposit.Creation.HistoricalTxRaw",
    "Lift.BeaconDeposit.Creation.HistoricalTxRecover", "Lift.BeaconDeposit.Creation.HistoricalTxSettle",
    "Lift.BeaconDeposit.Creation.HistoricalTxTrace", "Lift.BeaconDeposit.Creation.HistoricalWalk",
    "Lift.BeaconDeposit.Creation.Walk", "Lift.BeaconDeposit.DepositArgs", "Lift.BeaconDeposit.DepositDecode",
    "Lift.BeaconDeposit.DepositExec", "Lift.BeaconDeposit.Erc165", "Lift.BeaconDeposit.HistBeaconEnv",
    "Lift.BeaconDeposit.HistCommittedExec", "Lift.BeaconDeposit.HistCommittedHistory",
    "Lift.BeaconDeposit.HistDeployment", "Lift.BeaconDeposit.HistDepositEntries",
    "Lift.BeaconDeposit.HistDepositLogs", "Lift.BeaconDeposit.HistLadder", "Lift.BeaconDeposit.HistSafe",
    "Lift.BeaconDeposit.HistSafeCount", "Lift.BeaconDeposit.HistSafeGuards",
    "Lift.BeaconDeposit.HistSafeInsert", "Lift.BeaconDeposit.HistSafeNode",
    "Lift.BeaconDeposit.HistSafePubkeyRoot", "Lift.BeaconDeposit.HistSafeSignatureRoot",
    "Lift.BeaconDeposit.HistSafeWorld", "Lift.BeaconDeposit.HistoricalSeam", "Lift.BeaconDeposit.Init",
    "Lift.BeaconDeposit.Jumps", "Lift.BeaconDeposit.Ladder", "Lift.BeaconDeposit.Layout",
    "Lift.BeaconDeposit.Lift", "Lift.BeaconDeposit.LittleEndian", "Lift.BeaconDeposit.Liveness",
    "Lift.BeaconDeposit.Prog", "Lift.BeaconDeposit.Refines", "Lift.BeaconDeposit.RootLoop",
    "Lift.BeaconDeposit.RootView", "Lift.BeaconDeposit.Safe",
    "Lift.BeaconDeposit.SafeDecoder", "Lift.BeaconDeposit.SafeDispatch", "Lift.BeaconDeposit.SafeEvent",
    "Lift.BeaconDeposit.SafeGuards",
    "Lift.BeaconDeposit.SafeLittleEndian",
    "Lift.BeaconDeposit.SafeViews", "Lift.BeaconDeposit.Views",
]
# Contract-neutral modules the deployed-bytes deposit family uses, restored with it from the archive
# tag (receipt and log projections, historical SHA-256 walks, static-only In-frames).
SHARED += [
    "ExecutionBlockLogs",
    "ExecutionRetainedLogMembership", "ExecutionTransactionLogProjection",
    "Lift.HistPackedShaSize", "Lift.HistShaWalk", "Lift.PackedShaSize", "Lift.StaticOnlyFramesIn",
    "TransactionAdmissionProjection", "TransactionHistoricalForward",
]

# Shared declarations the deployed-bytes deposit family uses that left main with earlier releases,
# restored beside the modules whose vocabulary they extend (protocol-contract-corpus-v1).
SHARED += ["Lift.WalkKitSupport", "ExecutionHistorySupport", "TransactionForwardSupport"]

# Protocol-contract corpus source integration: shared vocabulary and narrow generic controls.
SHARED += ["Corpus.Freeze.RingCommon", "SystemCallEmpty", "Lift.RequestQueue.DrainLatency"]
CONTRACTS["beacon-roots"] = ["Corpus.Freeze.BeaconRoots", "Lift.BeaconRoots.Totality"]
CONTRACTS["history-storage"] = ["Corpus.Freeze.HistoryStorage", "Lift.HistoryStorage.Totality"]
CONTRACTS["beacon-deposit"].extend(["Corpus.Freeze.DepositCells", "Corpus.Freeze.DepositLedger"])
CONTRACTS["consolidation-request"].extend(["Lift.ConsolidationRequest.Occurrence"])

# Protocol-contract corpus Mac proof checkpoints: additive shared observers and family leaves.
SHARED += ["ExecutionKeptEntered", "Lift.EnvironmentInv", "BytesSliceNat"]
SHARED += ["ListFold", "ExecutionKeptFresh", "Lift.LogSilent"]
SHARED += ["Lift.SystemWordWriter", "RlpReceiptKeys", "ExecutionKeptReceiptLogs"]
SHARED += ["ExecutionKeptRuntime"]
SHARED += ["DepositRequestParser"]
CONTRACTS["beacon-roots"].extend([
    "Corpus.Proofs.BeaconRootsClassification", "Corpus.Proofs.BeaconRootsFrames",
    "Lift.BeaconRoots.Frame", "Lift.BeaconRoots.Read", "Lift.BeaconRoots.Writer",
])
CONTRACTS["history-storage"].extend([
    "Corpus.Proofs.HistoryStorage", "Lift.HistoryStorage.Frame", "Lift.HistoryStorage.Read",
])
CONTRACTS["beacon-deposit"].extend([
    "Lift.BeaconDeposit.LogCodec", "Lift.BeaconDeposit.LogOnly", "Corpus.Proofs.DepositLogShape",
])

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
    "Composition.BeaconRootsRetention": ('beacon-roots', 'history-storage'),
    "Composition.BeaconRootsSlotControl": ('beacon-roots', 'history-storage'),
    "Composition.Corpus.Proofs.RingHistory": ('beacon-roots', 'history-storage'),
    "Composition.Corpus.Proofs.RingValue": ('beacon-roots', 'history-storage'),
    "Composition.Corpus.Freeze.ConsolidationExecution": ('consolidation-request',),
    "Composition.Corpus.Freeze.ConsolidationJoint": ('consolidation-request',),
    "Composition.Corpus.Freeze.BuilderRequest": ('builder-request', 'withdrawal-request'),
    "Composition.Corpus.Proofs.ConsolidationExecution": ('consolidation-request',),
    "Composition.Corpus.Proofs.ConsolidationLatency": ('consolidation-request',),
    "Composition.Corpus.Proofs.RingTotality": ('beacon-roots', 'history-storage'),
    "Composition.DepositParse": ('beacon-deposit',),
    "Composition.DepositShortLogInput": ('beacon-deposit',),
    "Composition.DepositShortLogControl": ('beacon-deposit',),
    "Composition.RequestPhaseAmsterdam": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestCodesKept": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestClassification": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestControls": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestPublicObservers": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestPublicGuarantees": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestPublicFindings": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestPublicBounds": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestCarrier": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointG": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGFate": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGFateFocused": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGBalance": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGProvenance": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGLedger": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGPosition": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGRegistration": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGExitAuth": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGConservation": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGPaymentsTrack": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGPaymentsBlock": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGPayments": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGPaymentsAnchorCore": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGPaymentsAnchor": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGAppends": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGPush": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGChargeOnce": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGValue": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGOnboarding": ('builder-request', 'withdrawal-request'),
    "Composition.BuilderRequestJointGOnboardingWitnesses": ('builder-request',),
    "Composition.BuilderRequestJointGExitUnique": ('builder-request', 'withdrawal-request'),
    "Composition.RequestPhaseOrder": ('builder-request', 'withdrawal-request'),
    "Composition.RequestPhaseAmsterdamBal": ('builder-request', 'withdrawal-request'),
    "Composition.WithdrawalRequestFeeCounterexample": ('withdrawal-request',),
    "Composition.WithdrawalRequestFeeRefutation": ('withdrawal-request',),
    "Composition.WithdrawalRequestFeeHeadline": ('withdrawal-request',),
    "Composition.WithdrawalRequestDrainControl": ('withdrawal-request',),
    "Composition.ConsolidationRequestPublicObservers": ('consolidation-request',),
    "Composition.ConsolidationRequestPublicHeadlines": ('consolidation-request',),
    "Composition.ConsolidationRequestPublicHistory": ('consolidation-request',),
    # Every joint owner is explicit; no family or shared module may import back.
}

SHARED += ["ExecutionKeptStorageFold", "JointGloasReplayStep"]
COMPOSITION.update({
    "Composition.ConsolidationRequestPublicStorage": ("consolidation-request",),
    "Composition.DepositConsensusOutcomes": ("beacon-deposit",),
    "Composition.DepositPendingPass": ("beacon-deposit",),
    "Composition.BuilderRequestApplicability.Checks": ("builder-request",),
    "Composition.BuilderRequestActualFeeBounds": ("builder-request", "withdrawal-request"),
})

SHARED += ["ConcreteRunKept"]
COMPOSITION.update({
    "Composition.BuilderRequestApplicabilityCalls": ("builder-request", "withdrawal-request"),
})


# Reviewed protocol-contract corpus kept-history controls and observed-root adapters.
SHARED += ["SystemWordWriterKept", "KeptCreateAvoid"]
CONTRACTS["history-storage"].append("Lift.HistoryStorage.Writer")
COMPOSITION.update({'Composition.Corpus.Proofs.RingHistoryControls': ('beacon-roots', 'history-storage', 'withdrawal-request', 'consolidation-request'), 'Composition.Corpus.Proofs.RingRoots': ('beacon-roots', 'history-storage'), 'Composition.Corpus.Proofs.BuilderCheckpoint': ('builder-request', 'withdrawal-request'), 'Composition.Corpus.Proofs.BuilderObservedJoint': ('builder-request', 'withdrawal-request'), 'Composition.BuilderRequestApplicabilityInput': ('builder-request', 'withdrawal-request')})


# Reviewed guarded withdrawal-prefix and cap-one queue support.
SHARED += ['GloasWithdrawalPrefix', 'Lift.RequestQueue.Batch']
COMPOSITION.update({'Composition.BuilderRequestJointGDebitOnce': ('builder-request', 'withdrawal-request')})

# Reviewed D-S2 historical frame classification and mutant controls.
CONTRACTS["beacon-deposit"].extend([
    "Lift.BeaconDeposit.ClassifyRootView",
    "Lift.BeaconDeposit.ClassifyViews",
    "Lift.BeaconDeposit.HistEntryPrefix",
])
COMPOSITION.update({
    "Composition.DepositClassified": ("beacon-deposit",),
    "Composition.DepositClassifiedControls": ("beacon-deposit",),
})

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


LIVE_SET = os.path.join("scripts", "live-set.toml")


def live_set_failures(root, owner, found, contracts, compositions):
    """Checks (a) and (b) of the live set (`scripts/live-set.toml`).

    (a) CONTRACTS has exactly the live keys, and no released key appears in
        CONTRACTS or as a COMPOSITION family.
    (b) A module on disk that a release manifest lists and nothing live
        classifies fails by name, so a released family can't come back
        without a restore.
    -> (failures, number of live keys, number of released keys).
    """
    import json

    path = os.path.join(root, LIVE_SET)
    try:
        with open(path, "rb") as handle:
            table = tomllib.load(handle)
    except (OSError, tomllib.TOMLDecodeError) as exc:
        return [f"cannot read the live set {LIVE_SET}: {exc}"], 0, 0
    failures = []
    live = table.get("live")
    if not isinstance(live, dict) or not live:
        return [f"{LIVE_SET}: [live] must be a nonempty table of key = reason"], 0, 0
    for key, reason in live.items():
        if not isinstance(reason, str) or not reason.strip():
            failures.append(f"{LIVE_SET}: live key {key} has no reason")
    for key in sorted(set(contracts) - set(live)):
        failures.append(
            f"CONTRACTS has {key}, which {LIVE_SET} does not list as live — "
            f"list it under [live] or release it"
        )
    for key in sorted(set(live) - set(contracts)):
        failures.append(f"{LIVE_SET} lists {key} as live, but CONTRACTS has no such key")
    released = table.get("released", [])
    if not isinstance(released, list):
        return failures + [f"{LIVE_SET}: [[released]] must be an array of tables"], len(live), 0
    released_keys = {}
    for entry in released:
        if not isinstance(entry, dict):
            failures.append(f"{LIVE_SET}: a [[released]] entry is not a table")
            continue
        missing = [f for f in ("key", "tag", "commit", "manifest")
                   if not isinstance(entry.get(f), str) or not entry.get(f)]
        if missing:
            failures.append(f"{LIVE_SET}: [[released]] entry lacks {', '.join(missing)}")
            continue
        key = entry["key"]
        if key in released_keys:
            failures.append(f"{LIVE_SET}: {key} is released twice")
        released_keys[key] = entry
        if key in live:
            failures.append(f"{LIVE_SET}: {key} is both live and released")
        if key in contracts:
            failures.append(f"released key {key} ({entry['tag']}) is still in CONTRACTS")
        for mod, families in sorted(compositions.items()):
            if key in families:
                failures.append(
                    f"{mod} (composition) declares released family {key} ({entry['tag']})"
                )
        manifest_path = os.path.join(root, entry["manifest"])
        try:
            with open(manifest_path, encoding="utf-8") as handle:
                manifest = json.load(handle)
        except (OSError, ValueError) as exc:
            failures.append(f"{key}: cannot read release manifest {entry['manifest']}: {exc}")
            continue
        modules = manifest.get("modules") if isinstance(manifest, dict) else None
        if not isinstance(modules, list) or not modules:
            failures.append(f"{key}: release manifest {entry['manifest']} lists no modules")
            continue
        for mod in sorted(set(modules) & set(found)):
            if mod not in owner:
                failures.append(
                    f"{mod} belongs to released key {key} ({entry['tag']}) — "
                    f"restore the family or remove the module"
                )
    return failures, len(live), len(released_keys)


# ---------------------------------------------------------------------------
# Check 11 (2026-11-08, whitelist W4): shared documents name no contract family.
#
# README.md, PORTING.md, docs/COMMON_API.md and scripts/GATES.md describe the
# shared library and the gates; a family's uses of the shared API live in its
# claim-map file, docs/claim-map/<key>.md, which a release takes whole. A token
# `Blanc/X/Y.lean` or `Blanc.X.Y...` fails here when the module it names, or a
# directory whose modules all belong to one family, is a contract or
# composition module of any family, live or released (a released family's
# modules come from its release manifest). DOC_LAYERING_ALLOWED lists the lines
# that could not move without rewording; each entry must still match a
# violation, and the table's size is pinned by DOC_LAYERING_ALLOWED_COUNT.
# ---------------------------------------------------------------------------

SHARED_DOCS = ("README.md", "PORTING.md", "docs/COMMON_API.md", "scripts/GATES.md")
DOC_TOKEN = re.compile(r"Blanc(?:[./][A-Za-z0-9_'!?]+)+")

DOC_LAYERING_ALLOWED = [
    # The Amsterdam request-system paragraph names each family's instance next to the shared path.
    ("docs/COMMON_API.md", "`Blanc/Lift/BuilderRequest/SystemPath.lean`, family-local"),
    ("docs/COMMON_API.md", "is `Blanc/Lift/BuilderRequest/Latch.lean`."),
    ("docs/COMMON_API.md", "`Blanc/Lift/BuilderRequest/Delivery.lean`, family-local;"),
    ("docs/COMMON_API.md", "`Blanc/Lift/WithdrawalRequest/AmsterdamSystem.lean`,"),
    ("docs/COMMON_API.md", "`Blanc/Composition/RequestPhaseAmsterdam.lean`."),
]
DOC_LAYERING_ALLOWED_COUNT = 5


def family_modules(root, owner, found):
    """{module: family} for every contract or composition module, live or released."""
    import json

    families = {}
    for mod in found:
        category = owner.get(mod)
        if category == "composition":
            families[mod] = "composition " + ", ".join(COMPOSITION.get(mod, ()))
        elif category not in (None, "shared", "root"):
            families[mod] = category
    try:
        with open(os.path.join(root, LIVE_SET), "rb") as handle:
            released = tomllib.load(handle).get("released", [])
    except (OSError, tomllib.TOMLDecodeError):
        released = []
    for entry in released if isinstance(released, list) else []:
        try:
            with open(os.path.join(root, entry["manifest"]), encoding="utf-8") as handle:
                manifest = json.load(handle)
        except (OSError, ValueError, KeyError, TypeError):
            continue
        for mod in manifest.get("modules", []) if isinstance(manifest, dict) else []:
            families.setdefault(mod, f"{entry.get('key')} (released)")
    return families


def doc_layering_failures(root, owner, found):
    """-> (failures, number of shared docs read, allowed lines used)."""
    families = family_modules(root, owner, found)
    shared = {m for m in found if m not in families}
    owners = {}
    for mod in list(families) + list(shared):
        parts = mod.split(".")
        for i in range(1, len(parts)):
            owners.setdefault(".".join(parts[:i]), set()).add(families.get(mod, "shared"))
    directory = {d: next(iter(f)) for d, f in owners.items() if len(f) == 1 and "shared" not in f}

    def family(token):
        parts = token.removesuffix(".lean").replace("/", ".").split(".")[1:]
        for i in range(len(parts), 0, -1):
            prefix = ".".join(parts[:i])
            if prefix in families:
                return families[prefix]
            if prefix in directory:
                return directory[prefix]
        return None

    failures, used, read = [], set(), 0
    for doc in SHARED_DOCS:
        path = os.path.join(root, doc)
        if not os.path.exists(path):
            continue
        read += 1
        with open(path, encoding="utf-8") as handle:
            lines = handle.read().splitlines()
        for number, line in enumerate(lines, 1):
            named = sorted({f for f in (family(t) for t in DOC_TOKEN.findall(line)) if f})
            if not named:
                continue
            allowed = [i for i, (d, needle) in enumerate(DOC_LAYERING_ALLOWED)
                       if d == doc and needle in line]
            if allowed:
                used.update(allowed)
                continue
            failures.append(
                f"{doc}:{number} names a module of {', '.join(named)} — a shared document "
                f"names no contract family; move the passage into that family's "
                f"docs/claim-map/<key>.md under \"Uses of the shared API\""
            )
    for i, (doc, needle) in enumerate(DOC_LAYERING_ALLOWED):
        if i not in used and os.path.exists(os.path.join(root, doc)):
            failures.append(f"DOC_LAYERING_ALLOWED entry no longer matches a violation in {doc}: "
                            f"{needle!r} — remove it")
    if len(DOC_LAYERING_ALLOWED) != DOC_LAYERING_ALLOWED_COUNT:
        failures.append(f"DOC_LAYERING_ALLOWED has {len(DOC_LAYERING_ALLOWED)} entries; "
                        f"DOC_LAYERING_ALLOWED_COUNT says {DOC_LAYERING_ALLOWED_COUNT}")
    return failures, read, len(used)


def load_root_generator():
    """scripts/generate-root.py, loaded beside this script."""
    import importlib.util

    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "generate-root.py")
    spec = importlib.util.spec_from_file_location("root_generator", path)
    if spec is None or spec.loader is None:
        raise SystemExit(f"REGRESSION — layering: cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


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

    # Checks 8 and 9: the live set (scripts/live-set.toml) agrees with
    # CONTRACTS, and no released family's module is back on disk.
    live_failures, n_live, n_released = live_set_failures(
        root, owner, found, CONTRACTS, COMPOSITION
    )
    failures.extend(live_failures)

    # Check 10: Blanc.lean matches its generator (scripts/generate-root.py).
    failures.extend(load_root_generator().check(root, sys.modules[__name__], owner))

    # Check 11: shared documents name no contract family.
    doc_failures, n_docs, n_allowed = doc_layering_failures(root, owner, found)
    failures.extend(doc_failures)

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
        f"{INVENTORY_DOC} matches its generator; "
        f"live set: {n_live} key(s) live, {n_released} released; "
        f"Blanc.lean matches its generator; {n_docs} shared document(s) name no "
        f"contract family outside {n_allowed} listed line(s)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
