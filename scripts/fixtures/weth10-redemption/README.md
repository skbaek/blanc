# WETH10 redemption transaction fixtures

These two generated Prague `blockchain_tests` execute the exact
`Blanc.Weth10.weth10MainnetCode` runtime through full transaction and receipt
processing. Pinned EELS `t8n` fills the consensus goldens and Jaune replays the
committed blocks under `scripts/check-weth10-redemption.sh`.

`01-type2-redemption.json` contains three canonical EIP-1559 type-2
transactions with empty access lists, zero top-level value, and no
authorizations: `withdrawTo(recipient,0)` succeeds,
`withdrawTo(recipient,3)` succeeds, and the following
`withdrawTo(recipient,8)` is accepted for processing but inserts a failed
receipt because only seven booked units remain. Generator assertions pin the
exact booked/ETH effects, sender nonce and fees, coinbase tip, two burn logs,
and rollback/no-log result of the failed execution.

`02-authorization-mutation.json` is intentionally outside that flagship
profile. A valid type-4 authorization is signed by the withdrawal recipient
and delegates it to a one-byte `STOP` program. Preprocessing changes the
recipient from absent/code-free nonce zero to delegation code
`0xef0100 || delegate` and nonce one before WETH10's internal value call. The
transaction happens to succeed; the evidence is not that authorization cases
fail, but that nonempty authorization preprocessing materially changes the
code/nonce facts used by the type-2 proof.

Every case must have a positive generator assertion count. `manifest.json`
pins the exact two filenames, transaction types, receipt-success vectors, and
the authorization mutation class. The gate additionally byte-checks the
embedded WETH10 runtime before invoking Jaune.

Never hand-edit the JSON fixtures or manifest. Regenerate them with:

```sh
PYTHONPATH="$HOME/execution-specs/src" \
  "$HOME/execution-specs/venv/bin/python" \
  scripts/gen-weth10-redemption-fixtures.py
```
