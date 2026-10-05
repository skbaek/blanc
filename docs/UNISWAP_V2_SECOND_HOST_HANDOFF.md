# Uniswap V2 Pair: second parallel-host handoff

This is the current allocation of the remaining work. It supersedes the ownership
allocation in `UNISWAP_V2_PARALLEL_HOST_HANDOFF.md`; the first host's return and its
supporting reports remain historical evidence. This allocation does not waive any
goal condition, and U7's storage-key negative control remains required.

## Exact branching point and start procedure

The commit introducing this document is the shared fork. Its parent is
`8e10cca4ef94cc0f664049c37c51a036a28353a6`. The fork is published as
`origin/codex/uniswap-v2-second-host-fork`; that branch is a fixed start reference.
The original host continues on `codex/uniswap-v2-pair-bytecode-v1`. Create a fresh
feature branch for the new lane; do not reuse the completed first lane's branches.

From your Blanc clone, fetch the fork and create a separate goal worktree:

```sh
git fetch origin codex/uniswap-v2-second-host-fork
git worktree add .worktrees/uniswap-v2-second-host -b worker/uniswap-v2-second-host FETCH_HEAD
```

Record the full fetched commit ID before editing. Use your host's Creme launch
root, configured goal store, ownership/admission procedure, `doctor`, and complete
`host-guidance`; original-host paths, caches and limits are not portable.

Blanc's normal Git-pinned Jaune dependency is
`780ad71a07787527cc074e06696d0e6a742ba104` in both Lake files. Keep it. The original
host has prepared a proof-only Jaune candidate
`2737c8ebcaec2f3a9a7014156403300bc664daab`, but its publication, isolated combined
census and adoption await a separate user decision. It is not an available
dependency of this fork. Never substitute a sibling path or symlink.

Both previous lanes are already integrated: merge `e780185a` contains the original
host's work and `claude/uv2nh-integration-proposal` at `7cf9c841`, including returned
lane `d8f2c238`. Parent `8e10cca4` additionally fixes actual STATICCALL/precompile
classification in skim. Do not redo completed first-lane work.

The uncompleted U7 draft was removed from source before this fork; its only
occurrence had no downstream callers. It is preserved privately by the original
master. There is no `sorry` placeholder and no new Lean source in this fork.

## Workload and blanket ownership rule

Target allocation: roughly **55–60% of expected remaining proof effort and time
to the new host**, with 40–45% retained here. This is a planning estimate, not a
measured completion percentage or a wall-clock promise. Mint/swap and permit
authentication are the largest new-host packets; history and reachable gas are
the largest original-host packets. Review balance at green checkpoints rather
than using file counts as a proxy for proof work.

**Every remaining proof whose purpose is to construct a concrete EVM execution
with an adverse outcome belongs to the new host.** This applies to newly
discovered obligations as well as those named below, regardless of entry point,
file location, or which positive theorem motivated the control. It includes
counterexamples, failure/revert witnesses, loss-of-invariant witnesses, bad-callee
witnesses and actual-execution/model-mismatch witnesses. The original host may
consume returned evidence but does not author these witnesses. Positive execution
existence for liveness is a separate responsibility and stays with the original
host, apart from supporting positive components needed for the new host's frames.

The new host also owns the whole remaining goal-level negative-control portfolio,
including purely model/arithmetic controls that do not construct an EVM execution.
This rule does not turn every model control into a new bytecode-execution project:
prove the evidence altitude the goal actually requires. Retain and review already
completed controls instead of duplicating them. Gate implementation self-tests
and final gate orchestration stay here; any new concrete adverse EVM witness
needed by them must be supplied by the new host.

## New-host deliverables

### N1. Complete mint and swap frame refinement

Finish the actual pc-zero successful bytecode-to-typed-model consumers for mint
and swap, including all successful selector cases, exact Pair and foreign storage,
logs, return bytes, authentic observations and retained nested Pair turns.

For mint, start from `MintPrefixWalk`, `MintSource`, `FeeMintSource`, `FeeMintWalk`,
`MintAmountWalk` and `SqrtWalk`. Existing pricing/prefix/public-source results are
components, not a completed frame headline. Carry both balance observations and
the actual factory feeTo STATICCALL through the same execution; cover first mint,
later mint, protocol fee mint, address-zero minimum liquidity and final unlock.
Derive internal fee-acceptance and machine facts rather than exporting them as
new environmental assumptions.

Swap has no completed raw walk owner at this fork. Build its actual optimistic
transfers, conditional callback, post-callback balance queries, checked pricing,
packed update, logs, final unlock and exact output. Preserve actual callback ABI
bytes and variable data length. The observed balances must be those after the
transfers and callback, not selected independently from another execution.
Consume `PropertiesSwap`'s model laws rather than restating them.

Preserve `NoShrink` as an explicitly named economic premise; unconditional
refinement must not require it. The original master has adopted transfer-aware
Burn coverage (`incoming balance <= final balance + payout`) under the goal's
delegated premise-form decision. Do not silently change that form in model work.

Return the frame consumers and any positive compiled/gas component schedules
needed by them. The final reachable-state gas theorem is original-host work.

### N2. Authentic permit recovery turns and observation provenance

Close the first return's delegated address-1 recovery-view disclosure. The current
permit source inversion gives a plain `Ninst.Run`; recover the actual occurrence
and filled slot from the **same pc-zero Exec**, using the existing cursor cuts.
Carry views at the nonce-incremented state, the actual code-existence bit and real
child returns, including the case where the Pair address itself is 1.

Reuse the actual static-call adapter presently in `SkimCanonical` by moving the
Pair-specific part below permit and locked supply, for example into
`StaticViewTurns`. Keep neutral inversion in the common library. Merely allowing
arbitrary nonempty recovery queues in `LockedAuth` is insufficient: its current
interface does not authenticate them against the supplied incoming machine/Exec.
Strengthen or supplement `PairFrameOutcome` with same-execution observation and
retained-projection evidence. Preserve rollback pruning and original raw paths.

Send an early, narrow interface commit for this change, before finishing the
large frame portfolio, so the original host can consume it in history work.

### N3. All remaining goal-level negative controls and adverse executions

| Obligation | Required work / existing evidence |
|---|---|
| U7 storage-key control | Prove the genuine storage-key alias control; the existing repeated-footprint-list-key theorem does not satisfy it. Reuse `ApproveSource`'s actual raw approval refinement and write image, the shared finite ledger sum and storage read/write laws. This is conditional on an allowance/balance storage alias, not a claim to have found a Keccak collision. Preserve its independence from the positive ledger/history proofs. |
| U3(ii) mint rounding | Complete a checked **mutated model driver** in which successful later-mint quotients round up. The current pricing-seam witness in `ModelControls` is partial. Preserve original guards, first-mint root/minimum behavior, nested continuations and default production semantics. Avoid cloning the entire driver. |
| U2 refinement control | Supply one of the goal's specified model mismatches; upward Burn payout is the planned route. Use the completed Burn frame consumer when actual frame correspondence is needed. The original host supplies that positive consumer; no independent duplicate Burn walk. |
| U3(i) omitted NoShrink | Review/reuse `noShrink_required` and its reached prefix. Strengthen only if the final claim's statement requires it. Any corresponding adverse EVM execution proof belongs here. |
| U4 uint112 guard | Review/reuse `swap_uint112_control`; connect to the final claim at its required altitude. Any concrete reverting EVM witness belongs here. |
| U5 timestamp wrap | Review/reuse the modular-time control and ensure it addresses the final exact law, rather than only a weak intermediate statement. Any new witness belongs here. |
| U6 callee premise | Supply the required premise-deletion/failing-callee control at the goal's stated altitude; constructive adverse executions, if needed, belong here. |
| U1/U8 identity controls | Existing certificate mutation and wrong-salt/init-hash controls are already present. Retain them and identify their evidence; do not regenerate them unnecessarily. |
| Later obligations | The blanket rule above governs any additional adverse execution, reentry, rollback, decoder, arithmetic or resource witness identified during either lane's work. |

Model-control source starting points are `ModelControls`, `PropertiesSwap`,
`PropertiesOracleLaw` and `Creation/Facts`. A reached typed-model result is not
automatically an EVM execution witness: distinguish the two honestly in the
return report. A conditional universal theorem is also not an established
existential execution. Do not weaken a required statement to avoid that gap.

### N4. Consolidate the duplicate transfer helper

Remove the duplicate generic stages in `SkimTransferWalk` by consuming the
pointer-generic API already exposed by `SafeTransferWalk`. Preserve the actual
memory image, output/foreign-world semantics, full physical reply and decoder.
The returned helper uses Wf/PtrWord and a lower pointer bound of 96; the original
uses PtrMem and 128. Derive the bridge from the actual extended memory; do not
assume alignment from Wf or alter the final environment. Use the existing neutral
word-addition fact instead of the duplicate `skimOffset` wrapper where applicable.

`SafeTransferWalk` is original-host-owned and its public pointer-generic API is
the fork interface. If a missing shared lemma is needed, propose an additive
common-library change in a separate commit; do not rewrite Burn consumers.
The original host retains the actual strong skim moved-pointer reply-bound
discharge and the pending Jaune dependency work.

### N5. Portable WETH9 composition adapter (U10)

Build the WETH9-side adapter discharging token success/storage and the relevant
NoShrink premises from the corpus's actual WETH9 execution/history theorems.
Keep USDC environmental. Consume verified execution histories with authentic
observations; do not replace composition by unrelated synthetic witnesses or
assume token success as the result to be proved. Return a clear input interface
for the original host's final Pair-history theorem. Final exhibit instantiation
against the merged history consumer stays with the original host. U10 remains
in scope; this allocation is not a promise that an incomplete adapter satisfies it.

## Original-host deliverables

1. Finish Burn's actual two-transfer execution, independent reply accounting,
   moved memory, suffix, frame refinement and final unlock. Retain Jaune work,
   required dependency proposals/census and actual skim pointer-fit discharge.
2. Complete all-selector configured committed-history replay from the actual
   deployment checkpoint, consuming returned frame/provenance APIs. Carry U3
   share value and exact protocol fee, U5 modular oracle and U7 ledger to history.
   Nested transitions enter at actual continuation seams; do not count them again
   after replaying their root. Bind recorded old reserves/timestamps to the prior
   committed state and time to the configured block header.
3. Finish U6's positive exact-gas liveness at reachable states, with internal
   memory/cost/sentry/acceptance facts derived and only callee ENV plus HASH-T
   remaining. Complete U9 positive transaction liveness and instantiate U10 with
   the new host's composition adapter. Route all adverse witnesses to N3.
4. Integrate the two lanes, reconcile shared wiring and consolidate remaining
   lock-prefix duplication, perform recursive declaration-necessity review, and
   prepare reserved final count and public-wording decisions.
5. Own every host-sensitive measurement: exact-candidate quiet elaboration,
   regression comparison, runtime/cost measurements, peak memory and the final
   four-bucket cost ledger. Own the complete content-valid gate catalogue,
   combined axiom audit, claim-map acceptance and final U11/U12 report.

## File ownership and interface exchange

| Surface | Owner |
|---|---|
| `Mint*`, `FeeMint*`, `SqrtWalk`, new `Swap*` and composition adapter modules | New host |
| `Permit*`, `StaticViewTurns`, `MutableTurns`, `LockedSupply` | New host; publish provenance interface early |
| `ModelControls`, `PropertiesLedger` negative control, other narrowly scoped control modules | New host |
| `Model`, `Consumption`, `Properties*` needed by mutants | New host for additive/control work; preserve the production API and behavior; propose breaking interface edits separately |
| `SkimTransferWalk`, helper reuse edits in `SkimSecondWalk`/`SkimCanonical` | New host for consolidation/adapter relocation only |
| `Burn*`, `SafeTransferWalk`, `BalanceCall*`, Jaune, new global history/gas/transaction consumers | Original host |
| Skim strong reply/pointer-bound consumers | Original host; deliver additive modules until N4 merges to avoid simultaneous edits |
| `CursorExact`, writer/update/core entry APIs | Stable fork interfaces; either lane proposes needed changes before editing shared consumers |
| New contract-neutral modules | Creating lane, common-library-first; registry/wiring changes in proposal commits |
| `Execution.lean`, `Check*.lean`, `Blanc.lean`, `lakefile.lean`, `lake-manifest.json`, `scripts/**`, common registries, public claim map/counts | Original host; new host returns isolated wiring proposals |

The adverse-execution rule takes priority over the file table: put a control for
an original-host entry in a new host-owned control module that imports the
positive API, rather than editing the original host's in-progress walk.

Exchange green interface commits in this order: N2 provenance boundary; N1 mint
and swap consumers independently; N4 helper consolidation; final N3 controls
needing Burn/history; N5 composition adapter. N3's independent controls can start
immediately. The original host can work on Burn, generic history and gas while
N1/N2 proceed. The last all-selector application, Burn-dependent control and
composition instantiation necessarily wait for their named interfaces.

No silent scope transfer: if a dependency requires changing this allocation,
record the exact proposed files and types and coordinate before both lanes edit
them. Keep production model entry types/default behavior stable when adding a
mutant, and return equality/compatibility evidence for any generalized driver.

## Acceptance contract and evidence

The authoritative goal is `goals/uniswap-v2-pair-bytecode-v1.md` in the configured
goal store. Its earlier published text is available in `skbaek/plans` at
`129ff1fb2a529f4c7f242f89272ebcaeb2bd5f00`; this handoff carries the current
allocation, explicit-simplification condition and undropped U9/U10 status.
Retrieve current goal/state from the master for any unresolved semantic question.

Preserve all 27 runtime selectors and covered forks, exact pc-zero refinement,
deployment-established INIT, one-checkpoint configured history, environmental
callee premises, trace-local HASH-T only, arithmetic floors and modular wrap.
No HASH-U, new axioms, `sorry`, `admit`, `native_decide` or increased ceilings.
All proof lines newly written or changed must use **explicit simplification
only**, such as `simp only [...]`, `simpa only [...]` and `dsimp only [...]`.
Add no definitions or lemmas to the default simp set and do not hide implicit
simplification behind automation or wrappers.

Read `scripts/GATES.md`, `docs/COMMON_API.md` and `docs/PROOF_RECIPES.md`. Use
Lean inspector/prover feedback and the owned-build wrapper through your local
Creme, never bare Lake builds. Generic-shaped facts require shared API search
and the common-library-first workflow. Do not import another contract's walk
to borrow a generic proof; actual WETH9 composition uses its verified contract
results through the composition boundary.

Use one required kernel statement control/mutation, with the prescribed bite
evidence; do not add fixture/differential campaigns for properties already
proved. Run proof size, duplication, debt, residue, trust, layering and other
applicable source gates, owned narrow builds and the registered axiom audit.
Record exact commands, terminal verdicts, source IDs and any inherited failures.
Propose new-module imports/registry rows separately so the master can integrate
them; a probe that omits a new module is not whole-candidate axiom evidence.

At parent `8e10cca4`, the full owned build and six affected source gates passed.
The registered union walk was standard-only (87,940 roots, 971 declaring modules,
114,039 visited constants, nine stricter claims). The complete audit still exits
1 at **1,523 actual versus 1,384 recorded leaves**; three catalogue module-count
quotations are also mismatched. These are reserved integration/publication
surfaces, not authority to alter counts to get green. Report them separately from
new regressions. Earlier eight-import/three-count repair approval does not
authorize arbitrary final count movements.

The original host's 972-module timing genesis finished with exit 0 and 8,369.8 s
aggregate elaboration; it had no regression comparison. Those figures are not
portable new-host acceptance evidence. Final clean merged timing remains owed.
Do not move pins, baselines, budgets, allowlists, goldens, timeouts, publication
wording or protected public contracts without the required exact decision.

## Return and merge

Return coherent commits descending from the exact fork, without history
rewrites, on a distinct feature branch. Publish only that agreed feature branch
or transfer a Git bundle; never push a default branch. Keep shared wiring edits
in a separate proposal branch/commit series based on the proof lane, as in the
first split. Do not write the original host's master records or canonical stack.

Add `docs/UNISWAP_V2_SECOND_HOST_RETURN.md` with: exact fork/tip IDs; owned files;
U/M condition-to-theorem map; source correspondence and observation provenance;
all negative controls and their evidence altitude; exact gate verdicts; interface
proposals; local resource figures clearly marked informational; and a prominent
**remaining obligations and disclosures** section. Do not claim an entire
outcome complete when only its model, prefix or conditional component is proved.
Wind down Lean using your host's prescribed task command and report `OK` before
returning the task.

The original host reviews and merges the lane and proposal, then runs the
combined owned build, all required exact-candidate checks, complete catalogue,
final quiet measurements and acceptance report. Neither lane's local green
status is final goal acceptance. No condition is dropped by this handoff.
