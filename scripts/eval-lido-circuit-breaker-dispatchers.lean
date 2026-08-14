-- Emit exact compiler-derived Lido dispatcher candidates for the W3/O4
-- Pareto benchmark.  This evaluator owns no runtime literal: every candidate
-- reuses the production endpoint functions and auxiliary table.

import Blanc.LidoCircuitBreakerCode

namespace Blanc.LidoCircuitBreaker.DispatcherBenchmark

open Jaune
open Jaune.Ninst Ninst

/-- Remove exactly the leaf-local `nonpayable` wrapper used by the baseline.
After W3 lands `funcs` may already expose the raw bodies; rebuilding both forms
below keeps the frozen pre-W3 candidate reproducible across that transition. -/
private def endpointBody : Func → Func
  | .next (.reg .callvalue) (.next (.reg .iszero) (.branch _ body)) => body
  | body => body

private def unguardedFuncs (dp : DeployParams) : List (B256 × Func) :=
  (funcs dp).map fun entry => (entry.1, endpointBody entry.2)

private def guardedFuncs (dp : DeployParams) : List (B256 × Func) :=
  (unguardedFuncs dp).map fun entry => (entry.1, nonpayable entry.2)

private inductive DispatchForm
  | balanced
  | linear
  | hybrid5444

private inductive GuardForm
  | none
  | twoBranch
  | compactOr

private inductive EndpointForm
  | leafLocalNonpayable
  | raw

private structure CandidateSpec where
  label : String
  dispatch : DispatchForm
  guard : GuardForm
  endpoints : EndpointForm

/-- The sole owner of selector topology.  `leaf` and `chain` contain endpoint
bodies directly; there is deliberately no endpoint-call/jump constructor. -/
private inductive DispatchPlan
  | fallback
  | leaf (word : B256) (body : Func)
  | chain (word : B256) (body : Func) (miss : DispatchPlan)
  | split (pivot : B256) (left right : DispatchPlan)

private def DispatchPlan.toFunc (k : Nat) : DispatchPlan → Func
  | .fallback => .call k
  | .leaf word body => pushB256 word ::: eq ::: (body <?> .call k)
  | .chain word body miss =>
      dup 0 ::: pushB256 word ::: eq :::
        ((pop ::: body) <?> miss.toFunc k)
  | .split pivot left right =>
      dup 0 ::: pushB256 pivot ::: gt :::
        (left.toFunc k <?> right.toFunc k)

private def DispatchPlan.selectorBranches : DispatchPlan → Nat
  | .fallback => 0
  | .leaf _ _ => 1
  | .chain _ _ miss => 1 + miss.selectorBranches
  | .split _ left right =>
      1 + left.selectorBranches + right.selectorBranches

private def DispatchPlan.fallbackCalls : DispatchPlan → Nat
  | .fallback => 1
  | .leaf _ _ => 1
  | .chain _ _ miss => miss.fallbackCalls
  | .split _ left right => left.fallbackCalls + right.fallbackCalls

private def DispatchPlan.selectors : DispatchPlan → List B256
  | .fallback => []
  | .leaf word _ => [word]
  | .chain word _ miss => word :: miss.selectors
  | .split _ left right => left.selectors ++ right.selectors

private def truthFlag (condition : Bool) : String :=
  if condition then "T" else "F"

private def DispatchPlan.pathTokens (selector : B256) : DispatchPlan → List String
  | .fallback => ["fallback"]
  | .leaf word _ =>
      [s!"e:{word.toNat}:{truthFlag (selector == word)}"]
  | .chain word _ miss =>
      let matched := selector == word
      s!"e:{word.toNat}:{truthFlag matched}" ::
        if matched then [] else miss.pathTokens selector
  | .split pivot left right =>
      let goesLeft := decide (selector < pivot)
      s!"p:{pivot.toNat}:{if goesLeft then "L" else "R"}" ::
        if goesLeft then left.pathTokens selector else right.pathTokens selector

private def balancedPlan : DispatchTree → DispatchPlan
  | .leaf word body => .leaf word body
  | .fork left right =>
      .split (leftmostFsig right) (balancedPlan left) (balancedPlan right)

/-- A compact equality chain.  Non-final matches pop the preserved selector;
the final equality consumes it directly. -/
private def linearPlan : List (B256 × Func) → DispatchPlan
  | [] => .fallback
  | [(word, body)] => .leaf word body
  | (word, body) :: rest =>
      .chain word body (linearPlan rest)

private def splitPlan (pivot : B256)
    (left right : DispatchPlan) : DispatchPlan :=
  .split pivot left right

private def firstSelector (entries : List (B256 × Func)) : B256 :=
  entries.head?.map Prod.fst |>.getD 0

/-- Two balanced comparison levels split the exact 17 leaves into 5/4/4/4
linear groups. -/
private def hybridPlan (entries : List (B256 × Func)) : DispatchPlan :=
  let first := entries.take 5
  let second := (entries.drop 5).take 4
  let third := (entries.drop 9).take 4
  let fourth := entries.drop 13
  let left := splitPlan (firstSelector second)
    (linearPlan first) (linearPlan second)
  let right := splitPlan (firstSelector fourth)
    (linearPlan third) (linearPlan fourth)
  splitPlan (firstSelector third) left right

/-- A deliberately larger two-branch/call guard retained as a measured loser. -/
private def twoBranchGuardedMain (dispatchBody : Func) : Func :=
  callvalue ::: iszero :::
    ((pushB256 4 ::: calldatasize ::: lt :::
        ((.call fallbackSlot) <?> (fsig +++ dispatchBody)))
      <?> .call fallbackSlot)

/-- Compact shared rejection boundary: nonzero value or fewer than four
calldata bytes takes the one inline empty-revert arm. -/
private def compactGuardedMain (dispatchBody : Func) : Func :=
  callvalue ::: pushB256 4 ::: calldatasize ::: lt ::: Ninst.or :::
    (Func.rev <?> (fsig +++ dispatchBody))

private def candidateSpecs : List CandidateSpec :=
  [ { label := "current-balanced", dispatch := .balanced,
      guard := .none, endpoints := .leafLocalNonpayable },
    { label := "wrapped-linear", dispatch := .linear,
      guard := .none, endpoints := .leafLocalNonpayable },
    { label := "two-branch-shared-balanced", dispatch := .balanced,
      guard := .twoBranch, endpoints := .raw },
    { label := "shared-balanced", dispatch := .balanced,
      guard := .compactOr, endpoints := .raw },
    { label := "shared-linear", dispatch := .linear,
      guard := .compactOr, endpoints := .raw },
    { label := "shared-hybrid-5-4-4-4", dispatch := .hybrid5444,
      guard := .compactOr, endpoints := .raw } ]

private def specFuncs (spec : CandidateSpec) (dp : DeployParams) :
    List (B256 × Func) :=
  match spec.endpoints with
  | .leafLocalNonpayable => guardedFuncs dp
  | .raw => unguardedFuncs dp

private def buildPlan (spec : CandidateSpec)
    (dp : DeployParams) : DispatchPlan :=
  let entries := specFuncs spec dp
  match spec.dispatch with
  | .balanced => balancedPlan (.ofSorted entries)
  | .linear => linearPlan entries
  | .hybrid5444 => hybridPlan entries

private structure BuiltCandidate where
  program : Prog
  plan : DispatchPlan
  dispatch : Func

private def buildCandidate (spec : CandidateSpec)
    (dp : DeployParams) : BuiltCandidate :=
  let plan := buildPlan spec dp
  let dispatch := plan.toFunc fallbackSlot
  match spec.guard with
  | .none =>
      { program := ⟨fsig +++ dispatch, aux⟩
        plan := plan
        dispatch := dispatch }
  | .twoBranch =>
      { program := ⟨twoBranchGuardedMain dispatch, aux⟩
        plan := plan
        dispatch := dispatch }
  | .compactOr =>
      { program := ⟨compactGuardedMain dispatch, aux⟩
        plan := plan
        dispatch := dispatch }

private structure FuncCensus where
  branches : Nat
  calls : Nat
  fallbackCalls : Nat

private def FuncCensus.add (left right : FuncCensus) : FuncCensus :=
  { branches := left.branches + right.branches
    calls := left.calls + right.calls
    fallbackCalls := left.fallbackCalls + right.fallbackCalls }

private def funcCensus : Func → FuncCensus
  | .branch left right =>
      let combined := (funcCensus left).add (funcCensus right)
      { combined with branches := combined.branches + 1 }
  | .last _ => { branches := 0, calls := 0, fallbackCalls := 0 }
  | .next _ rest => funcCensus rest
  | .call target =>
      { branches := 0
        calls := 1
        fallbackCalls := if target = fallbackSlot then 1 else 0 }

private def funcsCensus (functions : List Func) : FuncCensus :=
  functions.foldl (fun total func => total.add (funcCensus func))
    { branches := 0, calls := 0, fallbackCalls := 0 }

private def emitCandidate (label : String) (program : Prog) : IO Unit :=
  match Prog.compile program with
  | none => IO.println s!"{label} COMPILE-FAILED"
  | some code => IO.println s!"{label} {code.length} {code.toHex}"

private def candidateCode
    (spec : CandidateSpec) (dp : DeployParams) : Bytes :=
  (Prog.compile (buildCandidate spec dp).program).getD []

private def candidateWordOffsets
    (spec : CandidateSpec) (field : ImmutableParameter) : List Nat :=
  contiguousRunStarts <|
    differingByteOffsets 0 (candidateCode spec zeroDeployParams)
      (candidateCode spec (immutableMarkerParams field))

private def candidateOffsetsValid
    (spec : CandidateSpec) (field : ImmutableParameter) : Bool :=
  let template := candidateCode spec zeroDeployParams
  let marker := candidateCode spec (immutableMarkerParams field)
  let offsets := candidateWordOffsets spec field
  marker.length = template.length && !(offsets.isEmpty) &&
    differingByteOffsets 0 template marker = wordByteOffsets offsets

private def immutableName : ImmutableParameter → String
  | .admin => "admin"
  | .minPauseDuration => "min-pause"
  | .maxPauseDuration => "max-pause"
  | .minHeartbeatInterval => "min-heartbeat"
  | .maxHeartbeatInterval => "max-heartbeat"

private def emitCandidateFamily (spec : CandidateSpec) : IO Unit := do
  let built := buildCandidate spec officialParams
  emitCandidate spec.label built.program
  let independent := candidateCode spec independentConstructorArgs.toDeployParams
  IO.println s!"independent {spec.label} {independent.length} {independent.toHex}"
  for field in immutableParameters do
    let offsets := candidateWordOffsets spec field
    let encoded := if offsets.isEmpty then "-" else
      String.intercalate "," (offsets.map fun n : Nat => s!"{n}")
    IO.println (s!"candidate-offsets {spec.label} {immutableName field} " ++
      s!"{offsets.length} {encoded}")
  IO.println (s!"candidate-patch-valid {spec.label} " ++
    s!"{immutableParameters.all (candidateOffsetsValid spec)}")

private def dispatchName : DispatchForm → String
  | .balanced => "balanced"
  | .linear => "linear"
  | .hybrid5444 => "hybrid-5-4-4-4"

private def guardName : GuardForm → String
  | .none => "none"
  | .twoBranch => "two-branch"
  | .compactOr => "compact-or"

private def endpointName : EndpointForm → String
  | .leafLocalNonpayable => "leaf-local-nonpayable"
  | .raw => "raw-shared-guard"

private def emitTopology (spec : CandidateSpec) : IO Unit := do
  let built := buildCandidate spec officialParams
  let mainCensus := funcCensus built.program.main
  let dispatchCensus := funcCensus built.dispatch
  let endpointCensus := funcsCensus ((specFuncs spec officialParams).map Prod.snd)
  let totalCensus := funcsCensus (built.program.main :: built.program.aux)
  let selectorBranches := built.plan.selectorBranches
  let missFallbackCalls := built.plan.fallbackCalls
  let guardBranches := mainCensus.branches - dispatchCensus.branches
  let guardFallbackCalls :=
    mainCensus.fallbackCalls - dispatchCensus.fallbackCalls
  let directLeafCalls :=
    dispatchCensus.calls - endpointCensus.calls - missFallbackCalls
  let auditValid :=
    dispatchCensus.branches == endpointCensus.branches + selectorBranches &&
    dispatchCensus.calls == endpointCensus.calls + missFallbackCalls &&
    dispatchCensus.fallbackCalls ==
      endpointCensus.fallbackCalls + missFallbackCalls &&
    mainCensus.branches == dispatchCensus.branches + guardBranches &&
    mainCensus.calls == dispatchCensus.calls + guardFallbackCalls &&
    directLeafCalls == 0 && built.plan.selectors.length == 17
  IO.println (s!"topology {spec.label} intrinsic-branch " ++
    s!"{guardName spec.guard} {endpointName spec.endpoints} " ++
    s!"{dispatchName spec.dispatch} {guardBranches} {selectorBranches} " ++
    s!"{missFallbackCalls} {guardFallbackCalls}")
  IO.println (s!"ast-census {spec.label} {totalCensus.branches} " ++
    s!"{totalCensus.calls} {mainCensus.branches} {mainCensus.calls} " ++
    s!"{dispatchCensus.branches} {dispatchCensus.calls} " ++
    s!"{endpointCensus.branches} {endpointCensus.calls} " ++
    s!"{selectorBranches} {missFallbackCalls} {guardBranches} " ++
    s!"{guardFallbackCalls} {directLeafCalls} {auditValid}")
  for selector in built.plan.selectors do
    let path := String.intercalate "," (built.plan.pathTokens selector)
    IO.println s!"ast-selector-path {spec.label} {selector.toNat} {path}"

#eval show IO Unit from do
  let rawBodySaving :=
    ((guardedFuncs officialParams).map (compsize ∘ Prod.snd)).sum -
      ((unguardedFuncs officialParams).map (compsize ∘ Prod.snd)).sum
  IO.println s!"endpoint-guard-saving {rawBodySaving}"
  for spec in candidateSpecs do
    emitTopology spec
  for spec in candidateSpecs do
    emitCandidateFamily spec

end Blanc.LidoCircuitBreaker.DispatcherBenchmark
