# Lido OssifiableProxy frozen efficiency campaign

`performance-manifest.json` is the immutable campaign definition for the 25
primary cells in Proxy Pair Goal 4. It contains no Blanc measurements, score
output, baseline, optimized result, or threshold experiment. The manifest is
frozen before the first full-port Blanc result; changing any world, fixture,
cell order, scalar, denominator, or score rule requires an explicit successor
format and review rather than an in-place result-driven edit.

The manifest digest is SHA-256 over canonical JSON with the digest value set
to the empty string. Canonical JSON is UTF-8, lexicographically sorted object
keys, `,` and `:` separators, and ASCII escaping. The JSON is normative; this
README is a compact map of its resolved worlds.

## Common concrete environment

- Engine: clean `ethereum/execution-specs` commit
  `4198b9c5996713b268aed602739d5aa40e277694`, module
  `ethereum.prague`, fork Prague, network disabled.
- EELS environment: `EELS_ROOT` (default `~/execution-specs`),
  `venv/bin/python`, `PYTHONPATH=${EELS_ROOT}/src`, and
  `PYTHONDONTWRITEBYTECODE=1`.
- Direct-message allowance: 20,000,000 gas. Gas is input gas minus terminal
  `gas_left`, before intrinsic gas and refunds. CREATE includes init-code work
  and returned-code deposit.
- Proxy target: `0xf2e246bb76df876cef8b38ae84130f4f55de395b`, the nonce-zero CREATE address of
  creator/control-admin `0x7e5f4552091a69125d5dfcb7b8c2659029395bdf`.
- Forwarding/unauthorized caller: `0x2b5ad5c4795c026514f8317c7a215e218dccd6cf`;
  new admin: `0x6813eb9362372eef6200f3b1dbc3f819671cba69`.
- Canonical constructor implementation/admin:
  `0x6f6541c2203196feedd14cd2c09550da1cbeda31` and
  `0x8ea83ad72396f1e0cd2f8e72b1461db8eb6af7b5`.
- Runtime worlds directly install each side's own returned runtime at the proxy
  target and seed the same logical ERC-1967 state. Unossified worlds use the
  synthetic control admin above; ossified worlds replace only the admin word
  with zero. Unspecified accounts are absent and unspecified storage is zero.
- Protocol entry warming consists of caller, proxy target, coinbase, and all
  seventeen Prague precompiles (`0x01` through `0x11`). Cold forwarding adds
  nothing. Warm forwarding adds
  exactly the canonical implementation account and the proxy's implementation
  slot; its prestate is otherwise byte-for-byte identical.

The nonempty setup datum is the 32-byte padded marker
`OSSIFIABLE_PROXY_SETUP_V1`. Its mock stores that word in the manifest's
fixture slot under `DELEGATECALL`. The empty setup mock stores the distinct
`OSSIFIABLE_PROXY_EMPTY_V1` marker. Forwarding mocks either echo calldata on
success, revert empty, or echo calldata on revert. A3 uses literal one-byte
`STOP` code (`0x00`), so empty setup tests code existence without executing an
implementation body.

## Frozen cells

| Cell | Frozen concrete world | Named scalar |
|---|---|---|
| A1 | Side-owned runtime returned by successful canonical-empty CREATE; reference is 2,497 bytes. | Returned runtime bytes |
| A2 | Side-owned creation template before the 128-byte canonical-empty ABI suffix; reference is 4,207 bytes. | Creation-template bytes |
| A3 | Fresh direct CREATE, creator nonce 0, value 0, canonical `(implementation,admin,0x)` tuple, canonical implementation contains `STOP`, create-entry warm set. | Direct CREATE gas |
| A4 | A3 with the canonical 32-byte nonempty setup datum and `setup-nonempty` code; setup succeeds and writes the fixture slot. | Direct CREATE gas |
| F1 | Cold direct fallback from forwarding caller, value 0, 32-byte `0xfeedface…` calldata, echo-success implementation, 32-byte return. | Direct call gas |
| F2 | F1 plus exactly the implementation account and implementation slot warm facts. | Direct call gas |
| F3 | Cold F1 calldata with empty-revert implementation; outer revert data is empty. | Direct call gas |
| F4 | F3 plus exactly the two F2 warm facts. | Direct call gas |
| F5 | Cold fallback with fixed 256-byte `0xfeedface000102…fafb` calldata and echo-success implementation; return is the same 256 bytes. | Direct call gas |
| F6 | F5 with echo-revert implementation; revert data is the same 256 bytes. | Direct call gas |
| F7 | Cold receive from forwarding caller, empty calldata, value 1, echo-success implementation, empty return. | Direct call gas |
| C1 | Cold control state, control admin caller, `proxy__getAdmin()`; returns the synthetic control admin. | Direct call gas |
| C2 | Same cold state, `proxy__getImplementation()`; returns the canonical implementation. | Direct call gas |
| C3 | Same cold unossified state, `proxy__getIsOssified()`; returns encoded false. | Direct call gas |
| C4 | Control admin calls `proxy__changeAdmin(new-admin)`; exact `AdminChanged` log and only the admin slot changes. | Direct call gas |
| C5 | Control admin calls `proxy__upgradeTo(new-implementation)`; new account has `STOP` code, exact `Upgraded` log. | Direct call gas |
| C6 | Control admin calls `proxy__upgradeToAndCall(new-implementation,"",false)`; new account has `STOP` code and no child call occurs. | Direct call gas |
| C7 | Control admin calls `proxy__upgradeToAndCall(new-implementation,setup-data-32,false)`; nonempty setup delegatecall writes the fixture slot. | Direct call gas |
| C8 | Control admin calls `proxy__upgradeToAndCall(new-implementation,"",true)`; forced empty-calldata setup delegatecall writes the empty marker. | Direct call gas |
| C9 | Control admin calls `proxy__ossify()`; admin becomes zero and `AdminChanged` then `ProxyOssified` are emitted. | Direct call gas |
| N1 | Unauthorized forwarding caller attempts representative `upgradeTo`; exact `NotAdmin()` revert and no effects. | Direct call gas |
| N2 | Same caller and calldata in the ossified prestate; exact `ProxyIsOssified()` wins precedence over caller mismatch. | Direct call gas |
| N3 | Control admin calls `changeAdmin(0)`; exact inherited `ERC1967: new admin is the zero address` payload and rollback. | Direct call gas |
| N4 | Control admin calls `upgradeTo(no-code)` where the target account is absent; exact inherited not-a-contract payload and rollback. | Direct call gas |
| N5 | Control admin upgrades to echo-revert code with the common 32-byte setup datum; child data bubbles exactly and implementation write, log, and storage all roll back. | Direct call gas |

The order above is fixed and the denominator is exactly 25. A cell is scored
only after its semantic projection agrees. Blanc must use fewer bytes or gas
for a strict win; ties, losses, semantic mismatches, and instrumentation
failures are non-wins. The acceptance threshold is at least 13 strict wins.
