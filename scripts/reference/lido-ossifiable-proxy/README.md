# Lido OssifiableProxy reference inputs

This directory is the membership-sensitive, offline authority for the
OssifiableProxy port.  Ordinary `generate` and `check` runs never use the
network.  They verify every input path and digest, recompile the exact Standard
JSON input with the vendored solc 0.8.9 Emscripten build, compare the complete
compiler output byte-for-byte, and independently reconstruct the canonical
deployment input and returned runtime from two RPC captures.

The source authority is Lido core `v4.0.0` at commit
`17005714f151e5502c559932319a3f2f74ac2436`.  The dependency authority is
OpenZeppelin Contracts `v4.4.1` at commit
`6bd6b76d1156e20e45d1016f355d154141c7e5b9`.  The exact source, build,
deployment, compiler-manifest, compiler, compiler-input/output, and RPC bytes
are all committed below `inputs/`; an added, removed, renamed, or changed file
is a failure.

Run the focused offline closure from the repository root:

```sh
scripts/check-lido-ossifiable-proxy-reference.sh
```

Regenerate the canonical lock or compatibility skeleton only from admitted
inputs:

```sh
python3 scripts/lido-ossifiable-proxy-reference.py generate
python3 scripts/lido-ossifiable-proxy-compatibility.py skeleton > /tmp/OSSIFIABLE_PROXY_COMPATIBILITY.md
```

`refresh-rpc` is deliberately separate.  It writes candidate captures to a
caller-supplied directory and refuses to write inside this authoritative input
tree.  A candidate has no authority until its raw responses, cross-provider
agreement, and resulting input/lock changes are reviewed and admitted:

```sh
python3 scripts/lido-ossifiable-proxy-reference.py refresh-rpc --output /tmp/ossifiable-rpc-candidates
```

The admitted archival operators are dRPC and BlastAPI.  PublicNode was tested
for this acquisition and served the historical transaction, receipt, and
block, but rejected pinned-block `eth_getCode` without a personal token.  It is
therefore not counted as either of the two complete authoritative captures.

The compiler ABI contains an inherited `BeaconUpgraded(address)` declaration
because Solidity reports inherited event declarations.  OssifiableProxy has no
external or constructor path to the inherited internal beacon-upgrade routine.
The raw ABI is therefore preserved byte-for-byte for build provenance, while
the behavioral census and compatibility document intentionally contain the
three reachable event families required by the port contract:
`Upgraded(address)`, `AdminChanged(address,address)`, and `ProxyOssified()`.
