# Deployed-bytecode claim map

What Blanc proves about bytecode that is already on Ethereum mainnet, one
section per live contract family (Section 5). A released family is documented
at its release tag, listed in `scripts/live-set.toml`.
Every headline below names the theorem that carries it, the premises it needs,
and what it does not say. This page is about the exogenous bytes themselves.

Historical exhibits outside paper v2, including WETH9, Beacon deposit, Lido, Uniswap and Blanc-native programmes, are preserved in the [archived corpus](https://github.com/skbaek/blanc/blob/corpus-v1-20261105/docs/DEPLOYED_BYTECODE_CLAIM_MAP.md). The section and disclosure labels below retain their historical numbering. The archive is outside the live corpus and is not promised to build against later revisions.

**A Blanc theorem is a statement about Jaune's modeled semantics, not a
deployment audit** ([`SECURITY.md`](../SECURITY.md)). Nothing here says that a
contract is safe, that its Solidity or Vyper source is correct, or that a
proved property is the property a user cares about. Each statement is read in
Lean, in the file the map cites, before it is relied on.

## 1. How to read this map

- **Names and lines.** Every declaration is written fully qualified, followed
  by the file and line where it is declared, for example
  `Blanc.Separated.pair_self` (`Blanc/Separated.lean:31`). Names and lines are checked against the
  repository (Section 10). A name in a premise column that is *not* fully
  qualified is defined in Section 9.
- **Statement kinds.** *Safety* is a refinement or an invariant. *Live* is
  constructive: a successful `Exec` exists and its gas is exact. *Witness* is
  an existence statement; a conditional witness lists its premises. *Deploy* is a modeled deployment.
  Levels are *frame*, *message*, *transaction* and *history*.
- **Configured history.** `ConfiguredHistoryTrace cfg checkpoint future`
  [`Blanc.ExecutionTrace.ConfiguredHistoryTrace` (`Blanc/ExecutionHistory.lean:116`)] is a retained replay of validated
  blocks (system messages, transactions, withdrawals, requests) under a valid
  chain configuration, every block's fork in `CoveredFork`. "After any
  configured history" quantifies over all of them.
- **Covered forks.** `CoveredFork` [`Blanc.CoveredFork` (`Blanc/Semantics.lean:167`)] is Prague, Osaka, BPO1 and
  BPO2. **Amsterdam is not covered.**
- **This commit.** Every figure and line in this document describes the commit
  you have checked out. Bind a quotation to `git rev-parse HEAD`, not to a
  hash written here.

## 2. Artifacts

The runtime bytes are the lifted inputs in `scripts/lift/inputs/`; the codehash
column is recomputed from those files by the checker (Section 10), and each
creation transaction is recorded in the entry's `provenance` in
`scripts/lift/certificates.json`. A family file's Artifacts part states its rows,
their compilers from the certificate provenance, and how their runtime identity was
established.

**Canonical system contracts.** The shared configured-execution machinery names
the four canonical system contracts at their protocol addresses. Their bytes are the definitions in `Blanc.beaconRootsCode` (`Blanc/SystemContracts.lean:35`) and its neighbours; the SHA-256
column is the digest recorded in each definition's docstring.

| Contract | Address | Bytes | SHA-256 | Definition |
|---|---|---:|---|---|
| EIP-4788 beacon roots | 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02 | 97 | cb7bd3e115730f7d57c15cd892880ed517ff4421bf43dfc7591198868fffe31d | `Blanc.beaconRootsCode` (`Blanc/SystemContracts.lean:35`) |
| EIP-2935 history storage | 0x0000F90827F1C53a10cb7A02335B175320002935 | 83 | 41cd74981e0201f79ebca054c4e8102a7e6faa28ce015d0048ab2250c1222c67 | `Blanc.historyStorageCode` (`Blanc/SystemContracts.lean:46`) |
| EIP-7002 withdrawal requests | 0x00000961Ef480Eb55e80D19ad83579A64c007002 | 504 | 22ac79b68752353c9bfbc6213fee1ec168df0f5abd2336c9ec239fc324e370b7 | `Blanc.withdrawalRequestCode` (`Blanc/SystemContracts.lean:56`) |
| EIP-7251 consolidation requests | 0x0000BBdDc7CE488642fb579F8B00f3a590007251 | 414 | 99e3d84dc4a4440c78a64619a2b451c08654cc83b44441585cb6db159478d661 | `Blanc.consolidationRequestCode` (`Blanc/SystemContracts.lean:92`) |

That a real chain holds exactly these bytes at these addresses is **not**
proved or checked here. It is the premise `SystemCodeInstalled`
[`Blanc.SystemCodeInstalled` (`Blanc/SystemContracts.lean:165`)] that a consumer states. Only the EIP-7002 code
contains call-type bytes at all (offsets 67, 123, 128, 141, all PUSH data).

## 3. Trust base

| Component | What is trusted | Evidence |
|---|---|---|
| Lean toolchain `v4.35.0` | Kernel soundness | For every constant of every Blanc module, and therefore for every theorem this map cites, the reachable axioms are within `propext`, `Classical.choice`, `Quot.sound`; one from-scratch union walk (Section 8), not `#print axioms` or `collectAxioms` |
| Jaune revision `74564f4d` | That its EVM and transaction definitions match Ethereum | Not a theorem. Conformance, as reported by that Jaune revision's own README and not re-run here: **4,712/4,712** supported fixture files and **34,474/34,474** cases of the execution-specs mainnet corpus (`tests@v21.0.2`), Prague through BPO2 including configured fork transitions |
| Lift certificates | Nothing | The Python producers are untrusted. Each certificate is accepted only by its Lean `cert_check`, a kernel decision, against the literal bytes |
| Runtime identity | That the lifted bytes are the mainnet bytes | Recorded in each certificate's `provenance`, by `eth_getCode` agreement across separately operated public providers at one finalized block or by a source-verified record; each family file's Artifacts part states which. The codehashes in Section 2 are recomputed from the lifted files by the checker |
| Fork scope | — | `CoveredFork` is Prague, Osaka, BPO1, BPO2. Amsterdam is not covered. A family whose rows use a wider fork range states it in its file's disclosures; the Jaune conformance figures above begin at Prague |
| Chain arithmetic | Model bound | Configured traces carry total ETH plus withdrawals below 2^256 (`SumNof` at the checkpoint) |
| Signature recovery | Premise of the signature-generic transaction theorems | `recoverSender … = .ok E` is a premise of every theorem that quantifies over all signed transactions, since there is then no single signature to evaluate. For a concrete transaction the kernel evaluates recovery. |

## 4. Premise classes

Every theorem hypothesis below has one of these classes; these are not Lean
logical axioms, and a clean axiom audit does not discharge them. The table says
whether a class is acceptable and whether deployment establishes INIT.

| Class | Meaning | Acceptable in a headline? | INIT established by a deployment theorem? |
|---|---|---|---|
| CODE | Installed code and fork identity | Yes | — |
| INIT | Stated once, at the checkpoint | Yes, if shown inhabited, ideally by deployment | Per contract: column M5 of the summary matrix (Section 6) |
| ENTRY | Required at every entered frame | Only if environmental, never invariant-shaped | — |
| HASH-T | Exact separation of the hashes and keys actually computed or touched in the trace, including avoidance of fixed slots where stated | Yes when stated; narrower and amenable to finite checking with a concrete initial footprint. Computational collision resistance does not entail this exact fact; fixed-slot avoidance also concerns target/preimage behavior. No cryptographic reduction is proved. | — |
| HASH-B | Binding instances: `Separated f [traceValue, recordedValue]` (`Blanc.Separated` (`Blanc/Separated.lean:23`)) for a hash or trie function `f`, a value the trace itself computes and a recorded value checked in the kernel against a public commitment | Yes when stated. Finite (two values), trace-local, satisfiable (`Blanc.Separated.pair_self` (`Blanc/Separated.lean:31`)) and not refutable; in context it is equivalent to the equation it delivers, `f traceValue = f recordedValue → traceValue = recordedValue` (`Blanc.Separated.pair_iff` (`Blanc/Separated.lean:42`)). Its gain is epistemic: it fails only under a collision of `f` on those two values, not under bad supplied data. The `trie` instances are structural: no Merkle–Patricia reduction of `trie` to Keccak is proved. HASH-T's key separation is the same shape (`Blanc.SlotFootprint.freshKeys_iff` (`Blanc/Separated.lean:61`)). No universal injectivity premise is used | — |
| HASH-U | Exact separation quantified over all 2^160 addresses or indices | Needs justification; not established here. The finite domain does not make proof impossible. Under a random-function model of Keccak the estimated failure probability is about q·2^-94 per frame (q = written slots): **heuristic bound estimate only, with no reduction or bound proved** | — |
| ENV | Gas, warmth, depth, static flag, callee behaviour, trace-local exclusions (no authorization or CREATE at given addresses) | Yes when stated; better derived | — |
| ARITH | Numeric bounds | Yes | — |

The per-frame calldata bound (below 2^256) is not a premise of any history
theorem: it holds for every raw frame of every configured history on all
covered forks [`Blanc.ExecutionTrace.ConfiguredHistoryTrace.calldata_bound` (`Blanc/ExecutionTraceCalldata.lean:927`);
`Blanc.ExecutionTrace.ConfiguredHistoryTrace.frameAdmitted_calldata` (`Blanc/ExecutionTraceCalldata.lean:944`)], because
`tx.gas ≤ blockGasLimit < 2^63`. Frame-level (non-history) theorems still take
it as a hypothesis about their own `sevm`.

Shared system-code support remains live: `Blanc.ExecutionTrace.ConfiguredHistoryTrace.systemFrames_of_installed` (`Blanc/ExecutionTraceSystemCode.lean:274`).
An offset-blind `SpawnFree` exclusion cannot be assumed for the canonical EIP-7002
bytes: `Blanc.withdrawalRequestCode_not_spawnFree` (`Blanc/SystemContracts.lean:135`).
The shared finite separation checks retain their characterizations:
`Blanc.SlotFootprint.checkFaithfulOn_eq_true` (`Blanc/SlotFootprint.lean:71`) and
`Blanc.SlotFootprint.checkApartOn_eq_true` (`Blanc/SlotFootprint.lean:83`).

## 5. Per contract

- [EIP-7002 withdrawal requests](claim-map/withdrawal-request.md)
- [EIP-8282 builder requests](claim-map/builder-request.md)
- [EIP-7251 consolidation requests](claim-map/consolidation-request.md)

## 6. Summary matrix

Columns: **M1** pc-0 entry; **M2** history with the invariant carried from one
checkpoint; **M3** per-frame premises environmental only; **M4** hash
premises trace-local or none; **M5** INIT established by deployment; **M6**
liveness at a reachable state; **M7** transaction-level liveness; **M8** all
covered forks. ✓ met, ✗ not met, ~ partial (see the footnote), — not
applicable.

[b] it is not chained into a configured history,
and that the factory issues the `initialize` call is a premise (the run is
then constructed), since the factory's bytecode is not lifted.

## 7. Disclosures and limits

11. **Rolled-back frames are not claimed.** History invariants hold of the
    final storage regardless; per-frame committed claims
    (the committed invocation lists) say nothing of
    frames rolled back or under a rolled-back ancestor.

13. **Liveness frames are fresh frames** (empty stack and memory) at a state. Transaction-level witnesses are only those a per-contract section states explicitly, under their premises.

14. **`SystemCodeInstalled`.** The canonical system bytes come from a Jaune test fixture
    (Section 2). For EIP-7002 the 504-byte runtime is provider-corroborated: three separately operated RPC services
    returned bytes equal to `Blanc.withdrawalRequestCode` (recorded evidence, not re-fetched). For the other system
    contracts the mainnet identity per covered fork is not checked here. Theorems still take the code as a premise.

15. **Runtime identity is recorded, not re-fetched.** The provider agreement
    behind each lifted input is evidence in the certificate `provenance`; it is
    not reproduced by any gate.

## 8. Axiom guarantee

**The guarantee.** `scripts/AxiomCheck.lean` imports the `Blanc` library, the two
authoring modules `Blanc/ProofRecipeTactic.lean` and
`Blanc/ProofRecipesGenerated.lean` (deliberately unreachable from the library's
root import), and Jaune's `AxiomAudit`, and runs exactly one
`#union_axioms_of_modules Blanc`. Every constant of every imported
module named `Blanc` or `Blanc.…` is a root of **one from-scratch walk** over
`Environment.find?` (types, definition, theorem and opaque values, inductive
constructors) with **one shared visited set**; the `UNION-AXIOMS 'Blanc': …`
report line prints the exact root, module and visited figures. Elaboration
fails unless the **union** of the axioms reached is within `propext`,
`Classical.choice` and `Quot.sound`; an empty population, or a reached
constant absent from the environment, also fails. That bounds `sorryAx`,
`Lean.ofReduceBool`, the `native_decide` and `bv_decide` auxiliary axioms, and
any bespoke `axiom`, for every declaration at once. Lean's own `#print axioms`
and `collectAxioms` are not verdict sources (lean4#15226).
`scripts/axiom_audit.py` refuses the audit unless every `Blanc/**/*.lean`
module is reachable from the imports, so a module nothing imports cannot
escape the walk. It runs as part of `scripts/check.sh --no-build`
(`scripts/GATES.md`).

**Consequence for citation.** There is no per-theorem list and no
per-theorem axiom row. Every theorem this map cites is covered by the union
guarantee at the commit the audit ran on, and carries exactly that bound: none
of them is one of the stricter claims below. The sentence available to a paper
is: *every constant of the library, hence each cited theorem, reaches only
`propext`, `Classical.choice` and `Quot.sound`, by one from-scratch union walk
at commit `git rev-parse HEAD`.* The guarantee concerns axioms only: the
statements are those read in Section 5, and the walk is tied to Jaune's
walker, it does not sandbox arbitrary Lean (`scripts/GATES.md`).

**The 0 stricter claims** (`#expect_axioms NAME [set]`, each checked in both
directions by the same walker; a claim exists only together with the register
row or gate constant that states it; none concerns a deployed-bytecode theorem
of this map). The checker requires this table to equal the rows of
`scripts/AxiomCheck.lean` exactly.

| # | Declaration | Exact set | Stated by |
|---|---|---|---|

**The count.** The published number of results is the leaf search's count of
leaf theorems: theorems of a `Blanc.*` module that no other Blanc declaration
uses (`scripts/leaf_audit.py`, `scripts/GATES.md` "Leaf audit"), each covered
by the union walk. It is generated
into `scripts/leaf-count.json` (never hand-edited) and quoted by the README and
the sites. At this commit it is 1876 leaf results (1831 public, 45 private).
The review ledger separately records the last review; the audit reports new
or changed leaves. The count is a property of the library at a commit, not of any cited theorem;
a cited theorem that another theorem uses is simply not a leaf. Bind any
quoted figure to `git rev-parse HEAD`, as the README does.

## 9. Named premises and definitions

Names that the tables above write unqualified.

| Name | Declaration | Role |
|---|---|---|
| `CoveredFork` | `Blanc.CoveredFork` (`Blanc/Semantics.lean:167`) | the covered forks: Prague, Osaka, BPO1, BPO2 |
| `ConfiguredHistoryTrace` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace` (`Blanc/ExecutionHistory.lean:116`) | a retained replay of validated blocks under a valid chain configuration |
| `FrameAdmitted` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.FrameAdmitted` (`Blanc/ExecutionHistoryAdmission.lean:27`) | pointwise admission of every interpreter execution retained by a configured history, against a per-frame entry predicate |
| `SumNof` | `Blanc.SumNof` (`Blanc/LadderBase.lean:8`) | a total below 2^256 |
| `SystemCodeInstalled` | `Blanc.SystemCodeInstalled` (`Blanc/SystemContracts.lean:165`) | the canonical system-contract bytes are installed at their addresses |
| `NoAuthorityAt` | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.NoAuthorityAt` (`Blanc/ExecutionTraceCodeAt.lean:598`) | no authorization of any transaction of a configured history recovers to the given address |
| `SpawnFree` | `Blanc.SpawnFree` (`Blanc/ExecutionTraceSystem.lean:24`) | the code has no instruction that could spawn a child frame, read at every offset (false of the canonical EIP-7002 code) |
| `ShaReady` | `Blanc.Lift.ShaReady` (`Blanc/Lift/ExactWalkCutOps.lean:66`) | the SHA-256 precompile premises of a frame's world: address 2 undelegated and warm, a precompile of the fork |
| `HistFork` | `Blanc.HistFork` (`Blanc/HistoricalFork.lean:21`) | the historical extraction domain, Byzantium through BPO2, Amsterdam excluded |
| `StateInv` | `Blanc.ContractSpecSem.StateInv` (`Blanc/LadderSem.lean:86`) | the state invariant of a semantic contract spec (the semantic contract spec's state invariant) |
| `checkFaithfulOn` | `Blanc.SlotFootprint.checkFaithfulOn` (`Blanc/SlotFootprint.lean:66`) | decidable: each written key and each observed key with the same slot are the same key (a HASH-T instance on explicit lists) |
| `checkApartOn` | `Blanc.SlotFootprint.checkApartOn` (`Blanc/SlotFootprint.lean:78`) | decidable: no observed key has a slot in the given raw-slot list |
| `mapSlot` | `Blanc.Lift.mapSlot` (`Blanc/Lift/MapSlot.lean:19`) | the Solidity mapping slot `keccak(key ++ base)` |
| `HashAvoidIn` | `Blanc.LockExclusion.LockSpec.HashAvoidIn` (`Blanc/LockExclusion.lean:844`) | every frame of the pool running the lock code avoids the lock slot with its executed hashes (HASH-T) |
| `Book` | `Blanc.Lift.Token.Book` (`Blanc/Lift/Token/Core.lean:48`) | a token's pure book: an abstract ledger, the step of one entered frame's message, the decoded operation, balances, allowances and a well-formedness predicate; no storage layout |
| `BookLaws` | `Blanc.Lift.Token.BookLaws` (`Blanc/Lift/Token/Core.lean:62`) | the laws of a book that the composition consumes |
| `Core` | `Blanc.Lift.Token.Core` (`Blanc/Lift/Token/Core.lean:98`) | what a token's address answers along a configured history, under an instance-chosen trace-local premise |
| `IsEntry` | `Blanc.Lift.Token.IsEntry` (`Blanc/Lift/Token/Core.lean:85`) | a frame entered at the token: storage owner and code address are both the token |
| `Erc20Abi` | `Blanc.Lift.Token.Erc20Abi` (`Blanc/Lift/Token/Abi.lean:17`) | the book reads the standard `transfer` and `balanceOf` selectors as those operations, for every calldata of at least 68 (`transfer`) or 36 (`balanceOf`) bytes and below 2^256 |
| `SelfCaller` | `Blanc.Lift.Token.SelfCaller` (`Blanc/Lift/Token/SelfCaller.lean:18`) | every entry-frame child of a settled non-static frame at the token has the token as caller |
| `TransferLive` | `Blanc.Lift.Token.TransferLive` (`Blanc/Lift/Token/Core.lean:145`) | frame-level `transfer` liveness at an exact cost, at the worlds an instance accepts |
| `NeverSigner` | `Blanc.Lift.Token.NeverSigner` (`Blanc/Lift/Token/Signed.lean:41`) | no settled non-static entry of the token along a history has the given account as signer |
| `BookS` | `Blanc.Lift.Token.BookS` (`Blanc/Lift/Token/Signed.lean:20`) | a pure book with an authorizer function (`BookS.signer`) |
| `BookLawsS` | `Blanc.Lift.Token.BookLawsS` (`Blanc/Lift/Token/Signed.lean:25`) | the signature-variant laws of a book, admitting the holder's signature as a third authorizer |
| `StaticWordCallProfile` | `Blanc.Lift.StaticWordCallProfile` (`Blanc/Lift/ExactCallProfile.lean:93`) | a `STATICCALL` site answering the named word, with a debit and a successor fixed before the call's gas: the call's charge is exactly the debit |
| `MutableCallProfile` | `Blanc.Lift.MutableCallProfile` (`Blanc/Lift/ExactCallProfile.lean:104`) | a zero-value `CALL` site that succeeds and keeps the caller's storage, with a debit and a successor fixed before the call's gas |

## 10. Checking this document

`scripts/check-deployed-claim-map.sh` holds this page to the repository. It is
offline, elaborates no Lean, and runs in continuous integration before the
toolchain is installed. It requires that:

- every fully qualified `Blanc.…` name resolves, spelled in full, to a public
  declaration written in Blanc's sources (the lexical resolver of
  `scripts/axiom_audit.py`);
- every `path:line` reference is attached to such a name and points at a line
  of that file that declares it or belongs to its docstring;
- every repository file it cites exists;
- every other identifier-shaped code span that looks like a Lean name is still
  some declaration's name;
- the table of stricter axiom claims in Section 8 equals the `#expect_axioms`
  rows of `scripts/AxiomCheck.lean` exactly, in both directions, and the leaf
  count equals `scripts/leaf-count.json`;
- the Jaune revision, the Lean toolchain and the covered forks equal the
  repository's; the runtime sizes and codehashes of Section 2 equal the lifted
  input files, its creation transactions and blocks appear in the certificate
  provenance, and the system-contract sizes and SHA-256 digests equal the bytes
  written in `Blanc/SystemContracts.lean`; and each live family's own record checks,
  stated in its file, agree with their authorities;
- the page keeps its section structure, its required headline theorems and its
  load-bearing disclosures, and carries no process vocabulary.

The required headline theorems are also pinned by exact statement in
`scripts/ClaimCheck.lean` (gate `scripts/check-claims.sh`), together with the
definitions they are stated through whose bodies are themselves the claim (pinned
by unfolding) and the record types they use (pinned field by field), so a weakened
headline fails there although this checker elaborates no Lean. The retained required names and their physical source owners are listed by this
checker; the exact statement-pin population is owned by `scripts/ClaimCheck.lean`.
The reachable family
headlines retain their own pins. Pin counts are generated on the exact candidate.

Each of those pins is a definitional-equality check against the current
definitions it mentions, so on its own it does not see a definition below the
pinned layer change. `scripts/check-claim-hash.sh` covers that layer: in one run
it hashes with SHA-256 the full definitional closure of every pinned statement
and every unfolding pin in `scripts/ClaimCheck.lean` (a definition by its type
and body, a theorem by its statement only so that changing the proof of any theorem it reaches changes nothing, an inductive type by its whole mutual
block with the names of its types and constructors and its constructor types;
binder names and annotations are ignored, and a referenced constant contributes
its own hash, not its name) and compares each pin's root hash with the manifest
committed in `scripts/claim-pin-hash/`; a mismatch names the definitions whose
content changed and the pins they reach. Each pin is keyed by the constant its
proof applies or the definition it unfolds, with the statement's hash added when
several pins share that name, so adding a pin adds one entry, while re-proving a
pin through a different constant shows as one pin removed and one added. It
reads the built Lean artifacts and refuses to run unless they, Jaune's
included, are certified current for the sources.
Jaune's definitions are hashed in full like Blanc's, because its EVM semantics
are part of what every claim means: a change of the Jaune revision moves exactly
the pins whose meaning changed, and the check names the Jaune definitions that
moved; a Jaune revision change that moves no pin passes with a note only, and
the recorded Jaune revision is then refreshed in a reviewed update. The hash stops at the other pinned dependencies: a constant from the Lean
toolchain, Batteries or Mathlib counts as its name together with the toolchain
in `lean-toolchain` or the package revision in `lake-manifest.json`, so its body
is fixed by that pin rather than by the hash. A hash records change, not
weakening: a mismatch says that the meaning of those claims moved and must be
reviewed, not that they became weaker.

Every run also executes in-memory falsifiers, each of which must be rejected:
a misspelled declaration, a stale line, a wrong file, an orphan line reference,
a missing cited file, a stale bare name, a wrong leaf count, extra, missing and
wrong stricter axiom claims, a wrong codehash, runtime size and creation transaction
(on the first artifact row of a live family file, while one exists), a wrong
system-contract digest, a wrong Jaune revision, process vocabulary, a deleted
headline and a dropped disclosure; and each live family's own falsifiers, stated in
its file.
The stricter-row controls use a synthetic authority/table pair when the live
stricter-claim population is empty; equality with the real audit source remains
mandatory in both directions.

What the check does **not** do: it does not elaborate Lean or re-derive any
axiom set (its authority over axioms is `scripts/AxiomCheck.lean`, verified by
`scripts/check.sh`); it does not judge whether a row's prose is a fair summary
of its theorem, whether a premise list is complete, or whether the bytes in
`scripts/lift/inputs/` are the bytes on the chain; and it does not re-run the
conformance figures of Section 3.
