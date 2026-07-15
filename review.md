# Executive verdict

**Blanc is a genuinely valuable verification research prototype and a promising verified EVM IR/assembler. It is not yet a professional smart-contract language or production toolchain.**

Its strongest contribution is unusually integrated:

1. an executable EVM;
2. an inductive relational semantics;
3. a proved correspondence between them;
4. a compiler whose exact emitted runtime bytecode is related back to structured Blanc execution;
5. a WETH solvency invariant lifted through nested execution, transactions, blocks, RLP decoding, and chain reachability.

That is substantial research work. The main threat to its credibility is upstream: **the reviewed ELeVM currently contains multiple definite Ethereum consensus-semantic defects and its CI does not compile most of the implementation.** Until those are repaired, Blanc’s theorems are rigorous statements about an experimental EVM model, not yet reliable statements about Ethereum.

| Dimension | Assessment |
|---|---|
| Research novelty | High |
| Lean proof discipline | Strong |
| Compiler theorem | Valuable but one-sided |
| WETH theorem | Deep safety result, not functional correctness |
| EVM conformance | Currently unsafe to trust |
| Language usability | Pre-alpha |
| Performance | Reference implementation quality |
| Production readiness | No |

## Review scope

I reviewed:

- Blanc commit `718e724c288e90a2a27053a0015d0f88a9622921`
- its actual local ELeVM dependency at commit `9d5806176340a19ac4eb38ee4aa4807ea56f5023`
- ELeVM’s checked-in fixture baselines and CI configuration
- the official protocol specifications relevant to the identified fork bugs

No files were changed and no heavy build was run. Lean LSP diagnostics were clean for all five main Blanc modules. `lean_verify` reported only the usual `propext`, `Classical.choice`, and `Quot.sound` axioms for the four headline solvency theorems, with no `sorryAx`.

---

# 1. What is genuinely strong

## 1.1 Executable/relational correspondence

The inductive `Exec` relation begins at [`/Users/bsk/blanc/Blanc/Semantics.lean:646`](/Users/bsk/blanc/Blanc/Semantics.lean#L646), followed by substantial fuel-saturation machinery and the final equivalence at [`/Users/bsk/blanc/Blanc/Semantics.lean:1830`](/Users/bsk/blanc/Blanc/Semantics.lean#L1830).

This is one of the best parts of the project:

- ELeVM remains executable and testable.
- Contract proofs can use structural induction instead of unfolding a fueled interpreter.
- Fuel exhaustion is distinguished from semantic EVM errors.
- The equivalence closes the gap between “the evaluator returned this” and “there is an inductive execution derivation.”

Professional researchers would find this reusable beyond WETH.

## 1.2 The compiler theorem has the useful direction for safety

The compiler is at [`/Users/bsk/blanc/Blanc/Common.lean:220`](/Users/bsk/blanc/Blanc/Common.lean#L220), with its main proof at [`/Users/bsk/blanc/Blanc/Common.lean:1568`](/Users/bsk/blanc/Blanc/Common.lean#L1568) and wrapper theorem at [`/Users/bsk/blanc/Blanc/Common.lean:1701`](/Users/bsk/blanc/Blanc/Common.lean#L1701).

Conceptually, it proves:

> If the exact bytes produced by `Prog.compile` execute successfully, the result is described by the structured Blanc program.

That backward-simulation direction is excellent for safety proofs: the compiler cannot introduce an additional successful behavior outside the source semantics.

It is not full compiler equivalence, but it is a meaningful theorem rather than a ceremonial “compiler correctness” result over an abstract target.

## 1.3 The effect/frame machinery is a strong research artifact

The fieldwise `Devm.Rels` abstraction begins at [`/Users/bsk/blanc/Blanc/Semantics.lean:103`](/Users/bsk/blanc/Blanc/Semantics.lean#L103), with outcome, instruction-frame, and generic effect machinery spread through `Common.lean`, especially around [`/Users/bsk/blanc/Blanc/Common.lean:3566`](/Users/bsk/blanc/Blanc/Common.lean#L3566) and [`/Users/bsk/blanc/Blanc/Common.lean:5781`](/Users/bsk/blanc/Blanc/Common.lean#L5781).

This is arguably more reusable than the WETH proof itself:

- state effects are factored by machine/world components;
- preservation can be composed through nested calls and creates;
- both success and error outcomes can be framed;
- it provides a route toward generated opcode-effect theorems and modular program logic.

## 1.4 The WETH proof is much deeper than the README suggests

The local contract invariant is proved around [`/Users/bsk/blanc/Blanc/Solvent.lean:4050`](/Users/bsk/blanc/Blanc/Solvent.lean#L4050), then lifted through:

- raw execution;
- calls and creates;
- message processing;
- transactions;
- block bodies;
- state transition at [`/Users/bsk/blanc/Blanc/Solvent.lean:7261`](/Users/bsk/blanc/Blanc/Solvent.lean#L7261);
- arbitrary valid-chain reachability at [`/Users/bsk/blanc/Blanc/Solvent.lean:7292`](/Users/bsk/blanc/Blanc/Solvent.lean#L7292);
- RLP decoding and block admission at [`/Users/bsk/blanc/Blanc/Solvent.lean:7302`](/Users/bsk/blanc/Blanc/Solvent.lean#L7302).

This is emphatically not just an opcode-level toy Hoare triple. The external call in `withdraw` occurs after the token balance update, and the proof infrastructure reasons through nested execution rather than assuming callbacks are friendly.

## 1.5 Collision handling avoids a false global axiom

Balances occupy raw address slots. Allowances use `keccak(src || dst)`, and writes are rejected if the resulting key could be an address-keyed balance slot.

That is awkward at the contract level, but mathematically honest: it avoids claiming that Keccak is globally injective, which is false. For the narrow solvency invariant, the approach provides exact balance-versus-allowance disjointness.

## 1.6 ELeVM is a serious foundation despite its current defects

ELeVM covers much more than opcode stepping:

- calls and creation;
- transaction processing;
- RLP and trie logic;
- block validation and state transitions;
- withdrawals, blobs, transient storage, delegation-related state;
- several cryptographic primitives and precompiles.

The `Mach`/`Meta`/`World` state partition around [`/Users/bsk/elevm/Elevm/Execution.lean:873`](/Users/bsk/elevm/Elevm/Execution.lean#L873) is a good proof-engineering direction. So is:

```lean
Fueled := ExceptT ε Option
```

which separates meta-level fuel exhaustion from actual EVM errors.

---

# 2. What the WETH theorem actually proves

The core invariant at [`/Users/bsk/blanc/Blanc/Solvent.lean:11`](/Users/bsk/blanc/Blanc/Solvent.lean#L11) is essentially:

> Sum of token balances, plus native value currently pending in an active frame, is no greater than the contract’s native Ether balance.

The world-state invariant additionally assumes:

- the contract contains the exact compiled WETH runtime code;
- global Ether summation does not overflow;
- the solvency inequality holds.

The block theorem also carries a no-overflow bound on withdrawals.

## It proves

- No successful modeled execution can leave aggregate WETH balances undercollateralized.
- Arbitrary callers and calldata are covered.
- Reverts and nested calls are accounted for.
- The invariant survives transactions and valid block transitions.
- Donated or forced Ether does not break the invariant.

## It does not prove

- ERC-20 or WETH9 functional equivalence;
- correct returns, reverts, events, or ABI rejection behavior;
- `totalSupply = Σ balances`;
- correct allowance authorization;
- that every holder can successfully withdraw;
- absence of stuck funds;
- termination or freedom from out-of-gas;
- exact gas usage;
- full selector or storage collision freedom;
- init-code or deployment correctness;
- proxy or upgrade safety;
- correctness of ELeVM relative to Ethereum.

A contract that always reverts can be solvent. A contract that burns users’ token balances can also be solvent. That does not make this theorem weak; it means it should be described precisely as a **substantial safety invariant**, not “verified WETH” without qualification.

The compiler theorem has the same scope issue. `Func.Run'` makes all error cases `True` at [`/Users/bsk/blanc/Blanc/Common.lean:1171`](/Users/bsk/blanc/Blanc/Common.lean#L1171), so compiler correctness says nothing about failure behavior or gas.

I would rename `correct` to something like `compiled_success_refines` or `compile_sound_on_success`.

---

# 3. Findings that should block any conformance or production claim

These are not matters of taste. I would block a release on them.

## 3.1 EIP-7702 authorization processing is effectively dead

At [`/Users/bsk/elevm/Elevm/Execution.lean:4070`](/Users/bsk/elevm/Elevm/Execution.lean#L4070):

```lean
if ¬ (authorityCode.isEmpty ∧ isValidDelegation authorityCode) then
```

A valid delegation is a nonempty 23-byte value. Therefore `isEmpty ∧ isValidDelegation` cannot hold, its negation is always true, and every authorization is skipped.

The required condition is essentially:

```lean
if !authorityCode.isEmpty && !isValidDelegation authorityCode then skip
```

The official rule is that authority code must be empty or already delegated. [EIP-7702](https://eips.ethereum.org/EIPS/eip-7702) also requires transaction type `0x04` and specifies that delegation to a precompile must execute empty code rather than the precompile.

Related defects:

- Raw typed-transaction decoding handles only `0x01`–`0x03` at [`/Users/bsk/elevm/Elevm/Execution.lean:4603`](/Users/bsk/elevm/Elevm/Execution.lean#L4603), so raw type-4 transactions are rejected.
- `disablePrecompiles` is threaded through the state but never consulted.
- Delegated code is loaded from `msg.benv.state` rather than the updated `msgDelegation.benv.state` at [`/Users/bsk/elevm/Elevm/Execution.lean:4157`](/Users/bsk/elevm/Elevm/Execution.lean#L4157).

## 3.2 Prague blob constants are stale Cancun values

At [`/Users/bsk/elevm/Elevm/Execution.lean:682`](/Users/bsk/elevm/Elevm/Execution.lean#L682):

- update fraction is `3338477`, but Prague requires `5007716`;
- target blob gas is `393216`, but Prague requires `786432`.

These values are live in blob base-fee calculation, `BLOBBASEFEE`, fee validation, and header validation. [EIP-7691 specifies the Prague values](https://eips.ethereum.org/EIPS/eip-7691).

This is a consensus-level error, not dead configuration.

## 3.3 Required precompiles are registered but unimplemented

- Point evaluation at `0x0a` returns `"UNIMP"` at [`/Users/bsk/elevm/Elevm/Execution.lean:2766`](/Users/bsk/elevm/Elevm/Execution.lean#L2766). This precompile is required by [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844).
- The seven BLS12-381 precompiles at `0x0b`–`0x11` are dispatched but return “not implemented” at [`/Users/bsk/elevm/Elevm/Execution.lean:2778`](/Users/bsk/elevm/Elevm/Execution.lean#L2778). Their addresses and operations are defined by [EIP-2537](https://eips.ethereum.org/EIPS/eip-2537).

Therefore ELeVM cannot presently be described as feature-complete Prague semantics.

## 3.4 ECADD checks the wrong coordinate

At [`/Users/bsk/elevm/Elevm/Execution.lean:2581`](/Users/bsk/elevm/Elevm/Execution.lean#L2581), the bound condition checks `x1 < prime` twice and never checks `y1`.

The elliptic-curve constructor subsequently reduces through the finite-field representation, so a noncanonical `y1 + p` may be accepted as `y1`. This is a classic copy/paste consensus bug and needs a targeted regression vector.

## 3.5 BLOCKHASH history is constructed incorrectly

`getLast256BlockHashes` at [`/Users/bsk/elevm/Elevm/Execution.lean:4875`](/Users/bsk/elevm/Elevm/Execution.lean#L4875) removes the latest block before collecting parent hashes and thereby omits one recent hash.

For a chain `[b₀,b₁,b₂]`, the resulting sequence omits `H(b₁)`. This directly explains the two checked-in BLOCKHASH fixture failures.

## 3.6 Header and RLP validation have important gaps

Confirmed examples include:

- no absolute `< 2^63` protocol bound on block gas limit;
- withdrawal indexes converted with truncating `.toB64`;
- several typed-transaction fields converted before strict width validation;
- address decoding that can accept extra trailing bytes in one path.

These explain checked-in invalid-block failures and can cause malformed input to be rejected for the wrong later reason.

## 3.7 ELeVM CI does not compile ELeVM

[`/Users/bsk/elevm/Elevm.lean`](/Users/bsk/elevm/Elevm.lean) imports only `Elevm.Basic`. The library is the sole default target in [`/Users/bsk/elevm/lakefile.lean`](/Users/bsk/elevm/lakefile.lean); `Main` and `Execution` are not in that default dependency closure. CI merely invokes the Lean action and runs no fixtures.

In other words, standalone CI can be green without compiling:

- `Types`;
- `Hash`;
- `EC`;
- `Execution`;
- `Main`.

This is probably the most embarrassing professional-engineering issue in the repository because it explains how several obvious defects can persist.

## 3.8 The fixture oracle is too permissive

For expected-invalid cases, [`/Users/bsk/elevm/Main.lean:162`](/Users/bsk/elevm/Main.lean#L162) ignores the expected exception identity and accepts any broadly classified Ethereum or RLP exception.

It also silently skips every case whose network is not exactly `"Prague"` and does not assert that at least one case in the file ran.

The checked-in full baseline records:

- 2,970 PASS files;
- 10 FAIL files;
- 3 TIMEOUT files.

That is substantial testing effort, but the harness explicitly checks for **classification stability**, not conformance. The selected legacy fixture tree contains no meaningful coverage of EIP-7702, BLS12-381, EIP-7691, or point evaluation, which is why the worst bugs are invisible.

## 3.9 Two glaring executable-performance bugs

At [`/Users/bsk/elevm/Elevm/Execution.lean:743`](/Users/bsk/elevm/Elevm/Execution.lean#L743):

```lean
instance : Hashable Adr := ⟨fun x => x.2.2⟩
instance : Hashable (Adr × B256) := ⟨fun x => x.1.2.2⟩
```

The second hash ignores the storage key entirely. Every warmed storage key belonging to one contract enters the same bucket, degenerating hash-set operations toward linear scans.

Separately, Blake2F calls `iterRangeTrace` at [`/Users/bsk/elevm/Elevm/Execution.lean:2741`](/Users/bsk/elevm/Elevm/Execution.lean#L2741), emitting `dbg_trace` on every round despite a clean `iterRange` existing immediately below. This likely explains the committed max-round Blake2F timeout.

These are the sort of issues that a basic benchmark or hot-path review should catch immediately.

---

# 4. Blanc-specific weaknesses

## 4.1 The language is an untyped syntax tree

The core language at [`/Users/bsk/blanc/Blanc/Semantics.lean:84`](/Users/bsk/blanc/Blanc/Semantics.lean#L84) records neither stack height nor stack shape:

```lean
inductive Func
  | branch : Func → Func → Func
  | last : Linst → Func
  | next : Ninst → Func → Func
  | call : Nat → Func
```

Consequences:

- stack underflow remains a runtime EVM error;
- branch arms need not have compatible stack effects;
- `DUP`/`SWAP` validity is not guaranteed;
- tail-call input conventions are informal;
- WETH stack correctness lives in manually maintained comments.

The current `line_inv`, `prog_inv`, and prefix automation are impressive responses, but they are compensating for missing static information.

## 4.2 `Func.call` is not a conventional call

It is a static tail jump with no return continuation. Calling it `call` is especially confusing because `Ninst.call` is the actual EVM `CALL`.

This means any reusable helper followed by more work must be:

- inlined;
- manually written in CPS;
- cloned for each continuation;
- routed through a continuation dispatcher;
- or implemented with a dynamic return jump outside the current source discipline.

This will become the first major wall once contracts exceed WETH complexity.

## 4.3 Dispatch correctness is only a comment

`DispatchTree` at [`/Users/bsk/blanc/Blanc/Common.lean:1717`](/Users/bsk/blanc/Blanc/Common.lean#L1717) does not encode:

- sortedness;
- selector uniqueness;
- tree balance;
- ABI collision freedom.

The implementation merely comments that leaves must be ordered. A malformed manually written tree silently misdispatches.

The public API should accept a finite list/map, compute selectors, reject collisions, sort it, and generate a certified layout.

## 4.4 Compilation failures are opaque

`Prog.compile` returns `Option B8L`. A failure does not say whether the cause was:

- an out-of-range auxiliary index;
- a branch location above 16 bits;
- a layout failure;
- code too large for deployment.

Use `Except CompileError`.

The compiler also checks only its internal `PUSH2` address limit, not Ethereum’s deployed-code limit. [EIP-170 sets the current limit to 24,576 bytes](https://eips.ethereum.org/EIPS/eip-170). The reviewed WETH runtime evaluates to 866 bytes, but larger programs can compile despite being undeployable.

## 4.5 The WETH implementation has ABI deviations

These do not invalidate solvency but matter for compatibility:

- Non-deposit functions do not check `CALLVALUE = 0`; calls can silently donate Ether.
- Argument access uses `CALLDATALOAD` without length checks, so truncated calldata zero-pads missing arguments.
- Write functions reject dirty high 96 address bits, while `balanceOf` and `allowance` do not.
- Withdrawal requests zero gas and relies on the value-transfer stipend, excluding many modern smart-wallet recipients.
- Storage layout is custom and not Solidity/proxy compatible.
- The collision guard can theoretically reject a valid approval.

These are excellent examples of why a solvency proof is not a functional contract specification.

## 4.6 The global-balance sum is spec-only but looks executable

The `sum` implementation around [`/Users/bsk/blanc/Blanc/Common.lean:193`](/Users/bsk/blanc/Blanc/Common.lean#L193) ranges up to the maximum 160-bit address.

That is mathematically definable but operationally infeasible. It should either:

- be clearly marked and isolated as noncomputable/specification-only; or
- be replaced with a fold over finite world-state support plus a theorem connecting it to the total-function view.

Accidentally unfolding this in simplification would be disastrous.

---

# 5. Answers to the design questions you anticipated

## 5.1 BitVec/Fin versus hand-rolled numbers

**Yes for the proof-facing representation, but benchmark before replacing the execution backend wholesale.**

Current ELeVM `B256` is nested pairs of four `UInt64`s at [`/Users/bsk/elevm/Elevm/Basic.lean:73`](/Users/bsk/elevm/Elevm/Basic.lean#L73), followed by hundreds of lines of custom operations and lemmas.

Recommended architecture:

- semantic word: `BitVec 256`;
- address: a newtype around `BitVec 160`;
- modular arithmetic view: equivalence with `Fin (2^256)` where useful;
- optimized executor: possibly retain four `UInt64` limbs;
- prove every optimized primitive refines the `BitVec` operation.

This gives Mathlib/Core interoperability and much better proof ergonomics without assuming arbitrary-precision `BitVec` execution will outperform native limbs.

Use `Fin` for genuinely bounded indices—stack positions, opcode operands, typed labels, fixed-array indexes—not as a universal replacement for every number.

## 5.2 Tail calls, CPS, and code reuse

The current restriction is valuable but too severe as the only option.

Best progression:

1. **Inlining** for small/hot helpers.
2. **CPS/defunctionalization** for a no-dynamic-jump backend.
3. **Compiler-controlled return labels** for normal source calls.
4. Prove every return target belongs to a finite set of emitted labels and has the required stack signature.

The important distinction is not “static versus dynamic EVM opcode.” Blanc already emits `JUMP`. It is:

> compiler-proven label versus arbitrary attacker-controlled `Word256`.

A typed `Label Γ` that cannot be forged from a word preserves control-flow integrity without forbidding normal code reuse.

EOF-style `CALLF`/`RETF`, if supported by a target revision in the future, would offer another backend.

## 5.3 Stack-effect IDE

This is probably the single highest-leverage developer feature.

Because Blanc is currently embedded in Lean, the first version does not need a separate language server. Add:

- a checked elaborator for instructions and blocks;
- `#stack_effect` or `#check_block`;
- Lean hover information showing before/after symbolic stacks;
- branch-join diagnostics;
- maximum stack depth;
- storage/memory/call/log effects;
- gas interval;
- source-to-bytecode PC mapping.

Then expose the same metadata through a VS Code widget/code lens. A standalone parser/LSP can follow later.

## 5.4 Huff users and binary-dispatch gas

Huff developers are indeed the highest-fit initial human audience: they already accept stack discipline and exact opcode awareness.

But they will immediately ask:

- Why is every branch `PUSH2`?
- Why can’t I choose dispatch layout?
- Where is the code-size/gas report?
- Where are macros, constants, tables, and helper returns?
- Can I inspect the exact emitted bytes?

Current branch lowering costs approximately:

- `PUSH2 + JUMPI`: 13 gas;
- plus `JUMPDEST` on the taken target: 14;
- an internal tail call including destination `JUMPDEST`: about 12 gas;
- a selector-tree fork adds `DUP`, `PUSH`, and `GT`, making it roughly 22–23 gas.

A balanced tree is not inherently a mistake. For ten functions it may be a sensible gas/code-size tradeoff. The mistake is offering only a manually constructed tree and no measurements.

Provide selectable or optimizer-chosen strategies:

- linear dispatch;
- balanced tree;
- weighted/hot-path tree;
- two-level table;
- validated perfect-hash/computed-jump strategy.

Also add minimal-width PUSH relaxation. It saves deployment bytes and code size, though not runtime PUSH gas.

## 5.5 Hash collisions in richer contracts

The present WETH guard solves only:

> allowance slot versus raw-address balance slot.

It does not solve:

- allowance versus allowance;
- mapping versus mapping;
- nested mappings and arrays;
- function selector collisions;
- CREATE2/address-hash assumptions.

Global Keccak injectivity must never become an axiom.

A scalable design should have:

1. a typed logical storage-layout IR;
2. structurally disjoint static namespaces;
3. domain-separated concrete slot allocation;
4. a theorem parameterized by `CollisionFreeOn` the finite set of reachable dynamic keys;
5. explicit computational collision-resistance assumptions in the threat model;
6. deterministic compile-time rejection for 4-byte selector collisions.

For balance/allowance separation specifically, reserving a high-bit namespace for hashed slots can remove the runtime balance-collision rejection, though dynamic hashed slots still require a collision assumption.

## 5.6 `Execution.lean` style

The goal of mirroring EELS is defensible. The current implementation is nevertheless too monolithic and brittle:

- 5,077 lines in one file;
- global string errors;
- manually threaded giant states;
- repeated full do-block inversion downstream;
- global constants for one fork;
- hot-path debug code;
- redundant record/update helpers;
- style comments forbidding `mut` and `for`, while pairing code uses both;
- comments containing “lopps,” “seams,” and “verificaiton.”

The right architecture is not “make the reference semantics aggressively imperative.” It is:

1. retain a readable EELS-like reference layer;
2. expose a small, stable theorem API around typed errors and state footprints;
3. implement a separate fast evaluator;
4. prove or translation-validate equivalence.

The existing `Mach`/`Meta`/`World` split is exactly the direction to continue.

## 5.7 Does AI make Blanc obsolete?

No—unless specification, proof generation, and model correctness all become essentially free.

Unstructured bytecode makes several things harder even for AI:

- proof search;
- modular lemma reuse;
- maintenance after code changes;
- audit diffs;
- gas reasoning;
- incident response;
- avoiding specification gaming.

WETH solvency illustrates the central AI risk: an AI can satisfy an incomplete theorem with a behavior humans never wanted.

The best future positioning is:

> **Blanc as a proof-carrying typed EVM IR for human- or AI-generated programs, plus a Huff-like surface language.**

A strong pipeline would be:

1. human or AI generates typed Blanc CFG and specifications;
2. verified baseline compiler emits bytecode;
3. AI superoptimizer may produce arbitrary optimized/spaghetti bytecode;
4. a small validator proves that bytecode refines the typed CFG;
5. raw EVM escape blocks are permitted behind local effect/spec obligations.

That makes Blanc infrastructure for the “final form,” rather than a competing crutch.

---

# 6. Three-tier roadmap

## Tier 1 — micro, hygiene, naming, organization

### Reproducibility and assurance hygiene

1. Replace [`/Users/bsk/blanc/lakefile.lean:12`](/Users/bsk/blanc/lakefile.lean#L12)’s `../elevm` dependency with an immutable revision; make a local override explicitly opt-in.
2. Make ELeVM’s real root import `Types`, `Hash`, `EC`, and `Execution`.
3. Run both the compiler/axiom gate and semantic fixtures in CI.
4. Require every selected fixture file to execute at least one case.
5. Check precise structured exception classes, not string prefixes.
6. State tested fork, EELS revision, fixture set, pass/fail/timeout counts, and unsupported features in the README.

### Names and namespaces

Put everything under `namespace Blanc` and `namespace Elevm`. Current generic root declarations such as `sum`, `correct`, `lift`, `fail`, `State`, `Exec`, `name`, `symbol`, and `selector` are collision-prone.

Rename:

- `Func.call` → `tailCall`;
- `kec` → `keccak256`;
- `delcall` → `delegatecall`;
- `statcall` → `staticcall`;
- `rev`/`ret` → `revert`/`return`;
- `exn` → `outcome` or `result`;
- `Nof`, `Fa`, `Wkn`, `spx`, `lpfx`, `pexen` to semantic names;
- `correct` to a directionally accurate theorem name.

`Stack.Push` and `Stack.Pop` are currently identical relations; use one split/frame relation with directional lemmas.

### Typos and stale comments

Confirmed examples:

- `totalSuppply` and `uptodate` in WETH;
- “op of the stack” in `Common.lean`;
- questionable “EIP-717” attribution for infinite approval;
- extra quotation marks in `"WETH"` comments;
- `lopps`, `seams`, `verificaiton`, `lnegth`, and “never will never” upstream;
- `ripemf160` in `Hash.lean`;
- upstream `Basic.lean` still describes definitions as useful for “Blanc.”

Remove process-history comments such as “Step 3,” “legacy retained,” and local line-number references. Git history is the archive.

### Stranded and duplicate code

Project-reference inspection found likely unused declarations including:

- `Bool.toChar`;
- `Overwrite`;
- `Except.IsError`;
- `toXinst_toB8`;
- `of_withPc_eq_ok`;
- `pushItem_delSets_eq`.

Also review the overlapping `Inv0`/`Inv1`/`Hinv0`/`Hinv1`, old success-only proof frameworks, and delete-set helper families. Deprecate first if external users may depend on them.

Delete the roughly 460-line commented hand-rolled arithmetic graveyard in Blanc `Basic.lean`, upstream’s duplicate pairing implementation, and unused debug/update alternatives.

### Formatting

`Common.lean` and `Solvent.lean` contain lines over 700 characters and hundreds of semicolon-heavy tactic chains.

Add a style/lint gate:

- 100–120 character target;
- stable indentation;
- spaces around type colons;
- one substantive tactic step per line;
- docstrings for public declarations;
- no commented-out implementation blocks.

### File organization

Blanc currently has 20,288 lines, with:

- `Common.lean`: 9,986;
- `Solvent.lean`: 7,332.

Suggested structure:

```text
Blanc/DSL/{Syntax,Combinators,StackEffect,Dispatch}
Blanc/Compiler/{Emit,Layout,Correctness}
Blanc/Semantics/{Relational,ExecutableBridge,Fuel}
Blanc/Proof/{Frames,Effects,Automation,Stack}
Blanc/Contracts/WETH/{Code,FunctionalSpec,Solvency}
Blanc/Ethereum/{Message,Transaction,Block}
```

ELeVM should similarly separate words, crypto, protocol revisions, VM components, precompiles, transactions, and blocks.

### Basic product hygiene

- Replace both `Hello World!` roots with a useful `compile/check/disasm` CLI or remove the executable.
- Keep `Blanc.lean` as a lightweight public API, not an import of the entire WETH solvency proof.
- Expand the README from a file inventory into installation, syntax, theorem scope, trust model, limitations, and a worked example.
- Snapshot the current 866-byte WETH runtime and its selectors/events in tests.

---

## Tier 2 — execution speed, typechecking, proof compression

### Immediate executable-speed fixes

1. Hash every address limb and storage key properly.
2. Replace Blake2F’s `iterRangeTrace` with `iterRange`.
3. Make disabled debug formatting lazy; current `cprint s!"{state}"` may construct the whole string before checking verbosity.
4. Predecode each code object once and cache:
   - instruction boundaries;
   - `JUMPDEST` bitmap;
   - PC-to-instruction mapping.
5. Replace repeated `List B8` slicing with `ByteArray`/array views.
6. Use amortized memory growth rather than allocating and copying the full buffer on each expansion.
7. Use an array-backed stack with cached height rather than repeated list length/index/update.
8. Accumulate logs, receipts, and request lists in reverse or in arrays/builders instead of `xs ++ [x]`.
9. Stop exponentiation once the exponent’s highest set bit has been processed rather than always running 256 rounds.
10. Add fast crypto/KZG backends behind a verified or differential-tested abstraction.

### Reference semantics versus fast semantics

Do not force one representation to serve all purposes.

Maintain:

- a pure, readable, proof-oriented EVM specification;
- a high-performance evaluator with arrays, cached decoding, and optimized crypto;
- a refinement theorem or translation validator between them.

Benchmark before and after. Lean’s pure `Array` updates can already exploit uniqueness, so “use mutation everywhere” is not itself a plan.

### Typechecking and proof length

The main problem is not simply “too much `simp`.” Roughly half of the existing `simp` calls are already `simp only`. The larger problem is repeated inversion of unfolded monadic do-blocks.

High-value changes:

1. **Audit changing `Exec : Type` to `Exec : Prop`.**  
   Current consumers wrap it in `Nonempty`; observed uses are propositional. This may reduce proof-object and `olean` cost, but benchmark and inspect `Exec.Pred` before committing.

2. **Replace deeply nested relation conjunctions with named structures.**  
   Current frame proofs contain brittle `.2.2.2...` projections.

3. **Build a monadic relational normalizer.**  
   The most useful general tactic would handle:
   - `Except`/`Fueled` binds;
   - assertions;
   - branches;
   - result mapping;
   - frame composition.

   Think `evm_wp`, `invert_exec`, and `frame`, not a larger global simp set.

4. **Unify the proof towers.**  
   Code preservation, balance preservation, and no-delete each repeat hundreds of lines of call/create case analysis. Extend the generic effect algebra until these become instances of one theorem.

5. **Generate opcode effect facts.**  
   Do not handwrite 67 storage-preservation instances. Maintain one declarative opcode footprint table and prove the generic classifier correct.

6. **Retire legacy success/error twins.**  
   Derive `getCode_eq`, `getCode_err`, `getBal_eq`, `delSets_eq`, etc. from one outcome-aware frame theorem.

7. **Make large proof implementations opaque behind a small theorem API.**
8. **Use scoped named simp sets** for EVM projections and state updates.
9. **Harden metaprogramming:** remove dependence on locals literally named `s`, raw string theorem lookup, fixed identifier capture, and `unsafe evalExpr` for numeric tactic arguments.
10. **Replace manually enumerated fuel-saturation depths** with a generic stability theorem or a small recursive-call IR.

No credible wall-clock proof profile emerged from the cached LSP profiler, so these recommendations are based on confirmed structural duplication rather than invented timing numbers.

### Compiler optimization

Low-hanging proof-producing or translation-validated passes:

- minimal-width PUSH relaxation;
- constant folding;
- peephole stack simplification;
- dead auxiliary and dead branch removal;
- inlining versus tail-jump choice;
- hot-path fallthrough layout;
- weighted selector dispatch;
- stack scheduling to reduce `DUP`/`SWAP`;
- exact code-size and symbolic gas reporting.

An optimizer need not be trusted if a small validator proves the optimized bytecode refines the typed CFG.

---

## Tier 3 — language design and complete toolchain

### 1. Replace the raw AST with a typed CFG

A serious next-generation Blanc core should encode:

- typed labels;
- block input/output stack signatures;
- verified branch joins;
- conventional internal returns;
- structured success/revert/exception effects;
- loops with invariants or bounded variants;
- maximum stack depth;
- read/write/call/log footprints.

A practical type might resemble `Block Γ Δ`, erasing to the current raw `Func`, with an erasure-correctness theorem.

Retain a raw-EVM escape hatch, but require local stack/effect/specification obligations.

### 2. Add modular external-call reasoning

Whole-world proofs will not scale to AMMs, bridges, hooks, smart wallets, or protocols.

Needed abstractions:

- typed call interfaces;
- assume/guarantee pre/post specifications;
- return/revert-data contracts;
- adversarial unknown-contract rules;
- call-trace predicates;
- reentrancy-aware frame or separation logic;
- callback capabilities.

### 3. Make ABI, events, and storage first-class

Must support:

- typed functions, tuples, arrays, bytes, strings, enums, booleans;
- strict versus permissive ABI decoding;
- encoder/decoder round-trip theorems;
- selector collision rejection;
- custom errors and revert decoding;
- typed events and indexed topics;
- typed mappings, arrays, packed storage, and namespaces;
- ABI JSON and storage-layout artifact generation.

### 4. Add a deployment story

Currently the theorem starts by assuming the runtime code is already installed.

Missing:

- init code and constructors;
- immutables;
- runtime/init linkage theorem;
- CREATE2 address derivation;
- library linking;
- deployment transaction generation;
- RPC deployment;
- on-chain code-hash attestation;
- an artifact recording Blanc, ELeVM, fork, compiler, and theorem revisions.

### 5. Support proxies and upgrades deliberately

The current fixed-code invariant does not directly cover proxy systems.

Needed:

- allowed/versioned code hashes;
- verified upgrade transitions;
- storage-layout compatibility;
- `DELEGATECALL` storage-context logic;
- admin/governance authorization;
- per-version invariant preservation.

### 6. Make fork evolution explicit

Use a `Revision`/`ForkConfig` parameter for:

- enabled opcodes;
- transaction types;
- gas schedule;
- precompiles;
- call/create/selfdestruct behavior;
- header validation;
- request processing.

Generate constants and feature tables from one versioned source where possible. Separate fork-independent proofs from small fork-specific lemmas.

### 7. Add an independent semantic trust layer

Axiom-free Lean code can still formalize the wrong machine—as the current EIP-7702 and ECADD bugs demonstrate.

Long-term assurance needs:

- an independent declarative specification;
- arithmetic-correctness theorems for word operations;
- `ZMod`/mathematical specifications for finite fields and curves;
- differential traces against EELS and production clients;
- property tests for encode/decode round trips;
- explicit isolation of any native crypto/KZG trust.

### 8. Complete the language toolchain

Must-have components:

| Area | Missing pieces |
|---|---|
| Frontend | Concrete syntax, parser, formatter, modules, macros |
| Static analysis | Stack/effect checker, gas/code-size analysis |
| Compiler | Diagnostics, linker, optimizer, translation validator |
| Artifacts | Bytecode, init code, ABI, storage layout, source maps |
| Testing | Unit, golden, fuzz, differential, official fixtures |
| Debugging | Disassembler, traces, source-PC mapping, debugger |
| IDE | Stack diagrams, hovers, effects, gas, proof obligations |
| Deployment | RPC, transaction builder, verification metadata |
| Verification | Functional specs, call interfaces, temporal properties |
| Ecosystem | Standard libraries, ERCs, access control, proxy patterns |

---

# 7. Recommended order of work

If I controlled the next several milestones:

1. **Semantic trust reset:** fix all confirmed ELeVM consensus defects.
2. **Make CI real:** compile the full ELeVM implementation and run precise conformance tests.
3. **Pin the dependency and document the exact trust model.**
4. **Add feature-complete Prague tests**, especially EIP-7702, EIP-7691, point evaluation, and BLS.
5. **State the WETH theorem honestly** and add differential ABI/behavior tests.
6. **Namespace and split the repositories** before further growth.
7. **Unify proofs around the outcome-aware effect algebra** and eliminate duplicate proof towers.
8. **Build the checked stack/effect elaborator and Lean IDE widgets.**
9. **Introduce reusable typed ABI/storage/event declarations.**
10. **Create the fast EVM backend**, starting with hashing, tracing, jump decoding, memory, and bytes.
11. **Move Blanc to a typed CFG with compiler-controlled return labels.**
12. **Add translation-validated gas/code-size optimization and the deployment artifact pipeline.**
13. **Then tackle modular external-contract reasoning, proxies, liveness, and broader functional correctness.**

# Bottom line

The central idea is good and should not be discarded. The exact-bytecode bridge, relational/executable correspondence, effect algebra, and chain-level WETH invariant are real accomplishments.

The current mistake would be to treat the first restrictive AST as the final language, or to treat ELeVM as a trusted Ethereum oracle because it is implemented in Lean. The best path is:

> Preserve Blanc’s proof boundary, rebuild the user-facing language around a typed CFG, and subject ELeVM itself to the same level of semantic verification that Blanc contracts receive.

That would make Blanc compelling not only to Huff developers, but also to formal-audit teams, protocol engineers, and AI systems that need a small, proof-carrying target for EVM code.