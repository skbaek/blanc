# Lifting a deployed contract: producer, certificate, checker

How the runtime bytes of an already-deployed contract become a kernel-checked `SFunc` program that Blanc proofs are
stated over, and what to touch when you add one. Everything here was read from `scripts/lift/lift.py`,
`scripts/lift/certificates.json` and the checked-in generated modules; where the producer's code and this page
disagree, the code wins. The proof kits that come after the checker are indexed in `docs/COMMON_API.md` section C9, and
tools and tactics in `docs/TOOLS.md`.

## The trust boundary

- The producer (`scripts/lift/lift.py`) is **untrusted**. It reads the runtime bytes and writes a certificate
  `Cert` (frame-relative control structure: one `Entry` per control context, each a tree of `SFunc` nodes), and
  optionally the Lean modules that decide it. It proves nothing.
- Acceptance is Lean's: `Cert.check code cert = true` (or `Cert.checkM code cert mems b = true` in memory mode), decided
  by the kernel in a `Check.lean`, plus `Cert.jumpsOk` for jump destinations. A wrong certificate is a failed build.
- `lift_sound` (`Blanc/Lift/Sound.lean`) turns every real `Exec` of that code into a run of the lifted program;
  `lift_exact` (`Blanc/Lift/Exact.lean`) is the gas-exact converse. Contract properties are proved over those runs.
- The registry (`scripts/lift/certificates.json`, schema `blanc-lift-certificates-v1`) pins each input by hash and
  records the committed outputs; `scripts/check-lift-certificates.sh` regenerates all of them and byte-compares.

## Pipeline, step by step

### 1. The input

- Put the runtime as hex text in `scripts/lift/inputs/<name>-runtime.hex` (a creation input goes in
  `<name>-creation.hex` and is a separate registry row). A leading `0x` is allowed.
- Record provenance: chain, address, the node(s) `eth_getCode` came from and the date, and for the deployed-bytecode claim
  map the creation transaction, block, deployer and nonce. `scripts/check-deployed-claim-map.sh` recomputes the byte
  count and keccak-256 from the file and requires the creation data to appear in the row's `provenance`.
- Two hashes are registered: `file_sha256` of the hex file and `runtime_sha256` of the decoded bytes
  (`runtime_bytes` is its length).

### 2. Probe the producer in lift mode (no registry)

```
python3 -B scripts/lift/lift.py --hex scripts/lift/inputs/X-runtime.hex --sha256 <runtime_sha256> \
  --namespace Blanc.Lift.X --cert-out /tmp/Cert.lean --check-out /tmp/Check.lean --report-dir /tmp/report
```

- It prints `Counts: entries=N, calls=…, nodes=…, loops=…, ext_calls=…, largest_entry=PC:NODES` and
  `Self-check verdict: PASS`. The verdict is the producer's own Python mirror of the checker; only Lean decides acceptance.
- `entries` chooses the assembly mode (step 4); `largest_entry` and `nodes` choose `split_nodes`; `--report-dir` writes
  `cert.json` and `cfg.json` for inspection.
- An opcode without a lifted transfer fails the run: the producer checks its opcode table (`LEAN_REG`) on every run
  against the arms of `ninstTransfer`/`liftRegularTransfer` (`Blanc/Lift/Transfer.lean`) and `regularTransfer`
  (`Blanc/AbstractStackTransfer.lean`). There is no way to assume one; extend the Lean transfer first.
- Everything below is also a registry key: `options` for producer behaviour, `check`, `jumps`, `tries`, `lock`, `fp`, `ws`
  for the generated modules, `code_*` for where the bytes live.

### 3. Producer options (registry `options` key; flag in parentheses)

All are off by default, so every row that omits them regenerates byte-identically.

- `fold` (`--fold`): fold ADD, MUL, SUB, LT, GT, EQ, AND, ISZERO over constant operands exactly as `foldConst` in
  `Blanc/Lift/Check.lean`. Used by solc-optimised code (the USDC and Uniswap V2 Pair rows). `fold_div_or`
  (`--fold-div-or`, needs `fold`) also folds unsigned DIV (zero divisor included) and OR.
- `pc` (`--pc`): lift PC as `SFunc.pcAt` (pushes the node's own pc). `decide_jumpi` (`--decide-jumpi`): a JUMPI with a
  constant condition keeps its live side and the dead side is `.undefined`, which `checkNode` does not check.
- `max_run` (`--max-run N`): name the rest of a straight-line `.next` run after N nodes; a long run of unoptimised code
  otherwise exceeds the elaborator's recursion depth (USDC V1 rows use 128).
- `join_entries: false` (`--no-join-entries`) and `wrapper_order: "fall-first"`: solc-w3 exploration switches, kept
  only so WETH9 regenerates byte-identically.
- `qualified_refs` (`--qualified-refs`): write the certificate's own `code`/`cert`/`mems`/`codeTries` fully qualified in the
  generated Check, CheckPart, CheckTries and Jumps modules (the Curve 3pool rows).
- Memory-tracking mode, Vyper-shaped code whose return tags travel through memory: `memret: "callnext"` (`--memret`),
  with `const_mem: true`, `entry_cap: K` and `widen: "agree"`. The map is a constant memory map whose transfer is exactly
  `absMem`/`memTop` (`Blanc/Lift/CheckMem.lean`); entries are keyed by constant state, at most K per control context (then
  widened to the constants all agree on); the producer also writes a `mems` list and a Check that proves `Cert.checkM` and
  `Cert.jumpsOkM`, which `lift_soundM`/`lift_exactM` consume. Note the defaults differ: the command line's
  `--entry-cap` defaults to 4, a registry row's `entry_cap` to 2; set it explicitly.
  - `frame_loops: true` (`--frame-loops`, with `const_mem`): unroll a Vyper 0.2.x frame save/restore loop, whose stack
    height changes every iteration. A back edge is then a revisit of the same pc at the same stack height, a constant
    JUMPI condition is decided in the pre-pass, and callee exploration follows a decided loop to its exit. Without it such
    a loop is closed as a loop entry. In use: the Curve 3pool row.
  - `mem_calls: true` (`--mem-calls`, memory mode): mirror `absMem`'s GAS and constant-output-window STATICCALL arms
    (GAS keeps the memory map; STATICCALL with a constant output window forgets only that window). Without it the map is
    forgotten there, which the checker accepts as a coarser map.
- Where the bytes live (`code_import`/`code_ref`, optionally `code_out`/`code_header`/`omit_code_def`): reference an
  existing canonical `ByteArray` instead of emitting another literal. The hex is still analysed; the kernel checks the
  referenced definition. `code_ref` must be qualified; `code_out` (with `code_header` and `omit_code_def`, only together
  with the reference pair) moves the literal into a generated data module. A single byte literal is emitted up to 6358 bytes
  (`CODE_LITERAL_MAX`, the largest that elaborates); larger runtimes become `++`-joined list chunks of 4096 bytes.

### 4. The `check` key: how `cert_check` is assembled

`check.path`/`check.header` name the generated `Check.lean`. Options of the generated checker:

- `split_nodes: N`: decide an entry above N nodes block by block (at unknown-condition branches). The producer's piece size
  is `CHECK_SPLIT_NODE_BUDGET` = 1000 nodes, the size a `decide +kernel` peaks under about 4 GiB at.
- `parts: N` (N ≥ 2): split into `CheckTries`, `CheckPart0..N-1` and an assembling `Check`. `rest_parts: K` (memory mode,
  `2 ≤ K ≤ parts`): move the tail of the `rest_`/`jrest_` assembly chain into `CheckRest1..K-1`.
- `literal_tries: true`: emit the code tries as data checked once against `LTrie.ofList`; `trie_build: true` (needs
  `literal_tries`): check each by one linear `LTrie.build` pass (`Blanc/Lift/CodeTriesBuild.lean`).
- `assembly`: how the per-entry decisions combine into `cert_check`. The choices, by entry count N:
  - none, N = 1: `Cert.check_singleton` (`Blanc/Lift/CheckAssembly.lean`), the sole `checkNode` decision.
  - none, N > 1: the generic conjunction, one membership case split; it exceeds the recursion depth for long certificates.
  - `"two"`: `Cert.check_two` (`CheckAssemblyPair.lean`); the producer insists on N = 2.
  - `"seven"`: `Cert.check_seven` (`CheckAssembly.lean`); N = 7 exactly.
  - `"chain"`: a chain over the tails `cert.drop k` (`Cert.checkAll_drop`, `Blanc/Lift/CheckChain.lean`), one entry per step;
    for certificates too long for the case split (USDC implementation: 180 entries).
  - Memory mode (`memret`) has no `assembly` choice: it always emits the chain `rest_i`/`jrest_i` over
    `Cert.checkEntriesM_drop`/`jumpsEntriesM_drop` and proves both `cert_checkM` and `cert_jumpsOkM` in the same modules.
- `jumps` (regular mode only: needs `check`, and memory mode has its jump decisions inside the Check): `jumps.path`, `jumps.header`; `assembly: "chain"` assembles
  `jumps_ok` over the tails; `paired: true` decides each entry's `checkNodeT` and `jumpsOkNodeT` in one `kernel_rfl_and`
  (`entry_jumps_i`; needs `check.parts ≥ 2`, no `split_nodes`, no `jumps.assembly`), because both walks evaluate the same
  abstract stacks.
- `tries` alone (no generated Check): a standalone `CheckTries.lean` beside a handwritten Check/Jumps (the beacon deposit
  contract). It cannot be combined with `check.parts ≥ 2`.
- A registry row with no `check` key has no generated Check: its Check is handwritten (the WETH9 and Curve 3Crv rows, per
  the registry's own note) or the row has none. The generated names the rest of the library uses are
  `cert_check`/`cert_checkM`, `entry_i`, `jumps_i`.

Cost, host-independent facts from the library's own docs: a 1,474-node entry of the 6,358-byte beacon deposit contract passed
16 GiB with plain byte reads and decides in 6 s / 3.4 GiB on the trie-reading copies `checkNodeT`/`jumpsOkNodeT`
(`Blanc/Lift/CheckFast.lean`, `docs/COMMON_API.md` C9). So every non-tiny certificate decides per entry with
`decide +kernel` through the tries; never one decision over a whole real contract.

### 5. Annotation producers (optional per row)

- `lock`: reentrancy-lock annotations (`scripts/lift/lockann.py`, checked by `Blanc/Lift/LockCheck.lean`'s `lockCert`);
  `spec` (slot, locked value, body and set/release pcs), `spec_module` (a handwritten `lockSpec`), `ann`, `check`, `header`.
- `fp`: free-pointer annotations (`scripts/lift/fp_annot.py`, `Blanc/Lift/FreePtr.lean`'s `fpCert`) and `ws`: write-site
  annotations (`scripts/lift/ws_annot.py`, `Blanc/Lift/WriteSite.lean`'s `wsCert`). Each gives `producer`, `namespace`,
  `ann`, and optionally `check_dir` with `parts` for the per-entry kernel-decision modules. The soundness theorems are
  `lift_sound_fp` and `lift_sound_ws`. All three producers are untrusted in the same way as `lift.py`.

### 6. Write, verify, build

```
python3 -B scripts/lift/lift.py --registry scripts/lift/certificates.json --write  --only <id>   # regenerate committed files
scripts/check-lift-certificates.sh                                                            # all rows, byte-compare, no Lean
```

Then build the family's `Check` module through your build wrapper (the kernel decides `cert_check` there). A row is
pure data: never hand-edit a `Cert.lean`, a registered `Check*.lean`, `Jumps.lean`, `LockAnn`/`LockCheck`, a `*/Ann.lean`
or a `Code.lean`; change the row or the producer and regenerate.

## Adding a family: what to touch, in order

1. Input hex, provenance, hashes (step 1); registry rows for the runtime and, if the creation is lifted, the creation input.
2. Probe (step 2), choose options (step 3) and the `check` shape (step 4); `--write --only <id>`.
3. Handwritten modules beside the generated ones: the `Jumps` for rows without `jumps`, the `Lift`/`Spec`/walk modules
   the family needs. Find a sibling of the same compiler and copy its shape: solc (`ExactWalkSolc`, Weth9, Uniswap V2
   Pair, USDC), Vyper 0.3.x with a lock (`VyperNonreentrantDeployed`, `VyperCallee`), Vyper 0.2.x memory mode
   (Curve3Pool, `VyperFrameLoop`), system contracts (`SystemContracts`, `WithdrawalRequest`).
4. Classification: every module must appear in `scripts/check-layering.py` (the family's `CONTRACTS` key; shared kits in
   `SHARED`), or `scripts/check-layering.sh` fails on an unclassified module.
5. Reachability: each module is in the import closure of `Blanc.lean` or listed in `scripts/AxiomCheck.lean`, which
   `scripts/axiom_audit.py` requires to import every Blanc module (so the union axiom walk sees it).
6. Docs and gates that name families: `scripts/GATES.md` (the `check-lift-certificates.sh` row lists the families; the
   self-counts are read by `scripts/check-doc-counts.sh`), the claim map `docs/DEPLOYED_BYTECODE_CLAIM_MAP.md`
   (artifact row, headline theorems; checked by `scripts/check-deployed-claim-map.sh`), the headline pins in
   `scripts/ClaimCheck.lean` (gate `scripts/check-claims.sh`). The README's lift bullet, the claim map and the site are
   published wording: ask the user's master before changing them.
7. Run: `scripts/check-lift-certificates.sh`, the family's `cert_check` builds, `scripts/check-layering.sh`,
   `scripts/check-doc-counts.sh`, `scripts/check-deployed-claim-map.sh`, then the full set from `scripts/GATES.md`.
   A new declaration nothing uses is a leaf: delete it or justify it (`AGENTS.md`).

## Tests of the producer itself

`python3 scripts/lift/test-code-reference.py` runs the source-emission and malformed-option controls for `code_import`/
`code_ref` (no Lean). The registry run is the real regression test for every other option.
