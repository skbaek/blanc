# TriggerableWithdrawalsGateway reference inputs

This directory is the immutable, offline authority tree for
`scripts/lido-twg-reference.json`.

Ordinary validation is network-free.  It verifies exact input-tree membership,
recompiles the thirteen-source Solidity closure with the vendored
`solc 0.8.9`, reconstructs the official and differential-world CREATE inputs,
patches the `LOCATOR` immutable at compiler-reported spans, and validates the
two archived mainnet RPC snapshots.

The admitted provenance route is **pinned-source compilation**.  The fact that
the official locator-patched runtime equals `eth_getCode` at the pinned block
is a dated selection snapshot, not a claim that Blanc verifies the deployed
Solidity contract or its historical deployment transaction.

Mechanical refresh is explicit and is never part of the ordinary gate:

```sh
python3 scripts/lido-twg-reference.py refresh-inputs \
  --lido-repo <clean lidofinance/core checkout at 17005714...> \
  --openzeppelin-repo <clean OpenZeppelin checkout at 6bd6b76...> \
  --soljson <verified solc 0.8.9 JavaScript binary> \
  --solc-list <verified one-build Solidity release manifest>

python3 scripts/lido-twg-reference.py refresh-rpc \
  --operator drpc --output <outside-this-tree>/rpc-drpc.json
python3 scripts/lido-twg-reference.py refresh-rpc \
  --operator blastapi --output <outside-this-tree>/rpc-blastapi.json
python3 scripts/lido-twg-reference.py admit-rpc \
  --drpc <outside-this-tree>/rpc-drpc.json \
  --blastapi <outside-this-tree>/rpc-blastapi.json
```

After review, the input hashes are pinned in the builder and the lock is
regenerated with `python3 scripts/lido-twg-reference.py generate`.  Neither
`generate` nor `check` contacts the network.
