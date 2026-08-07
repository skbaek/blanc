# WETH10 compatibility contract

This document freezes the ordinary-call public boundary of the WETH10 deployed
at `0xf4BB2e28688e89fCcE3c0580D37d36A7672E8A9F`. The generated lock in
`scripts/weth10-reference.json`, reconstructed from the deployment input and
the installed runtime, supplies the ABI keys and selectors. The embedded
deployed source supplies the source-level behavior. Current repository `main`
is drift evidence only.

The scope is empty-calldata receive and canonically ABI-encoded calls with
adequate execution gas. Unless a row says otherwise, a successful return is
standard ABI encoding of the listed outputs; a successful no-output call has
empty returndata. Any revert rolls back this contract's writes and logs, ETH
movement, callback effects, and child logs. A bubbled child revert retains its
returndata byte-for-byte. “Empty revert” means zero-length returndata from the
Solidity 0.7.6 dispatcher, code-existence check, or ABI return decoder, not a
new WETH10 reason.

Evidence remains **planned** until the later Blanc runtime, theorem, and
differential-fixture owners land. Owner abbreviations are:

- `DF-view`, `DF-state`, `DF-callback`, `DF-permit`, and `DF-flash`: planned
  deployed-vs-Blanc differential fixture families;
- `TH-read`, `TH-state`, `TH-callback`, `TH-permit`, and `TH-flash`: planned
  Blanc functional theorem families; and
- `TH-backed`: the backing-preservation family. It proves the invariant, not
  full endpoint behavior.

All arithmetic described as unchecked is modulo `2^256`, matching Solidity
0.7.6. Event notation lists indexed arguments before the data word.

## Runtime endpoints

<!-- WETH10-ENDPOINT {"signature":"CALLBACK_SUCCESS()","selector":"0x8237e538"} -->
### `CALLBACK_SUCCESS()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; output `bytes32`; selector `0x8237e538`. |
| Success | Returns `0x439148f0bbc682ca079e46d6e2c2f0c1e3b820f1a291b069d8882abf8cf18dd9`, the keccak of UTF-8 `ERC3156FlashBorrower.onFlashLoan`. No state, ETH, log, or external-call effect. |
| Guards/reverts | No source guard. Nonzero call value is rejected by the dispatcher before the getter with empty revert data. |
| Evidence owners | `DF-view`; `TH-read`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"DOMAIN_SEPARATOR()","selector":"0x3644e515"} -->
### `DOMAIN_SEPARATOR()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; output `bytes32`; selector `0x3644e515`. |
| Success | Reads `chainid()`. When it equals `deploymentChainId`, returns the cached deployment separator. Otherwise returns `keccak256(abi.encode(domainTypeHash, nameHash, versionHash, currentChainId, address(this)))` for domain `EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)`, name `Wrapped Ether v10`, and version `1`. No state effect. |
| Guards/reverts | No source guard or external call. Nonzero call value is an empty dispatcher revert. Contract-address correspondence and the three valid comparison worlds are frozen below. |
| Evidence owners | `DF-view`, `DF-permit`; `TH-read`, `TH-permit`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"PERMIT_TYPEHASH()","selector":"0x30adf81f"} -->
### `PERMIT_TYPEHASH()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; output `bytes32`; selector `0x30adf81f`. |
| Success | Returns `0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9`, the keccak of UTF-8 `Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)`. No effects. |
| Guards/reverts | No source guard. Nonzero call value is an empty dispatcher revert. |
| Evidence owners | `DF-view`, `DF-permit`; `TH-read`, `TH-permit`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"allowance(address,address)","selector":"0xdd62ed3e"} -->
### `allowance(address,address)`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; inputs `(owner: address, spender: address)`; output `uint256`; selector `0xdd62ed3e`. |
| Success | Returns the logical allowance for the ordered pair; no effects. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. The later tagged projection is trace-local for allowance-pair collision exclusion, as frozen below. |
| Evidence owners | `DF-view`; `TH-read`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"approve(address,uint256)","selector":"0x095ea7b3"} -->
### `approve(address,uint256)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(spender: address, value: uint256)`; output `bool`; selector `0x095ea7b3`. |
| Success/effects | Sets `allowance[msg.sender][spender] = value`, emits `Approval(msg.sender, spender, value)`, and returns encoded `true`. Zero spender and any value are accepted. |
| Guards/calls | No source guard or external call. Nonzero call value empty-reverts before the body. |
| Evidence owners | `DF-state`; `TH-state`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"approveAndCall(address,uint256,bytes)","selector":"0xcae9ca51"} -->
### `approveAndCall(address,uint256,bytes)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(spender: address, value: uint256, data: bytes)`; output `bool`; selector `0xcae9ca51`. |
| Pre-call state/log | Sets the allowance and emits `Approval(msg.sender, spender, value)` before the callback. |
| External call | Typed zero-value call to `spender` with `onTokenApproval(msg.sender, value, data)` (`0x00ba451f`). The callback observes the new allowance and emitted-log prefix. |
| Return/reverts | Returns the callback's ABI-decoded Boolean verbatim, including successful `false`. Child reverts bubble. A zero/codeless target, short returndata, invalid Boolean word, or otherwise failed return decode empty-reverts and rolls back the approval. Nonzero entry value empty-reverts before the body. |
| Evidence owners | `DF-callback`; `TH-callback`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"balanceOf(address)","selector":"0x70a08231"} -->
### `balanceOf(address)`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; input `(account: address)`; output `uint256`; selector `0x70a08231`. |
| Success | Returns the account's logical balance; no effects. Address zero and `address(this)` are ordinary lookup keys. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. |
| Evidence owners | `DF-view`; `TH-read`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"decimals()","selector":"0x313ce567"} -->
### `decimals()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; output `uint8`; selector `0x313ce567`. |
| Success | Returns `18`; no effects. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. |
| Evidence owners | `DF-view`; `TH-read`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"deploymentChainId()","selector":"0xcd0d0096"} -->
### `deploymentChainId()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; output `uint256`; selector `0xcd0d0096`. |
| Success | Returns the chain ID captured by the constructor. The installed mainnet instance returns `1`; a fresh Blanc deployment is parametric in its deployment chain. No effects. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. |
| Evidence owners | `DF-view`, deployment fixtures; `TH-read`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"deposit()","selector":"0xd0e30db0"} -->
### `deposit()`

| Field | Frozen behavior |
|---|---|
| ABI | `payable`; no inputs or outputs; selector `0xd0e30db0`. |
| Success/effects | The contract first owns `msg.value`; then unchecked-credits `balanceOf[msg.sender] += msg.value` and emits `Transfer(address(0), msg.sender, msg.value)`. Returns empty bytes. Zero value still follows the write/log path. |
| Guards/calls | No source guard or external call. The ETH increase and logical credit are both visible after success. |
| Evidence owners | `DF-state`; `TH-state`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"depositTo(address)","selector":"0xb760faf9"} -->
### `depositTo(address)`

| Field | Frozen behavior |
|---|---|
| ABI | `payable`; input `(to: address)`; no outputs; selector `0xb760faf9`. |
| Success/effects | Unchecked-credits `balanceOf[to] += msg.value`, emits `Transfer(address(0), to, msg.value)`, and returns empty bytes. Address zero and `address(this)` are accepted mint recipients. |
| Guards/calls | No source guard or external call. Zero value still emits. |
| Evidence owners | `DF-state`; `TH-state`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"depositToAndCall(address,bytes)","selector":"0x5ddb7d7e"} -->
### `depositToAndCall(address,bytes)`

| Field | Frozen behavior |
|---|---|
| ABI | `payable`; inputs `(to: address, data: bytes)`; output `bool`; selector `0x5ddb7d7e`. |
| Pre-call state/log | Contract balance already includes `msg.value`; unchecked-credits `balanceOf[to]`, then emits `Transfer(address(0), to, msg.value)`. |
| External call | Typed zero-value call to `to` with `onTokenTransfer(msg.sender, msg.value, data)` (`0xa4c0ed36`). The callback observes the credited balance, increased ETH balance, and log prefix. |
| Return/reverts | Returns the decoded Boolean verbatim, including `false`. Child reverts bubble. Address zero/codeless targets and failed Boolean decoding empty-revert and roll back the mint, log, and incoming ETH transfer. |
| Evidence owners | `DF-callback`; `TH-callback`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"flashFee(address,uint256)","selector":"0xd9d98ce4"} -->
### `flashFee(address,uint256)`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; inputs `(token: address, amount: uint256)`; output `uint256`; selector `0xd9d98ce4`. |
| Guard order | First require `token == address(this)` or revert with exact `Error("WETH: flash mint only WETH10")`. The amount is ignored. |
| Success | Returns `0`; no effects or calls. Nonzero entry value is rejected before the source guard with empty data. |
| Evidence owners | `DF-view`, `DF-flash`; `TH-read`, `TH-flash`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"flashLoan(address,address,uint256,bytes)","selector":"0x5cffe9de"} -->
### `flashLoan(address,address,uint256,bytes)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(receiver: address, token: address, value: uint256, data: bytes)`; output `bool`; selector `0x5cffe9de`. |
| Guard/order before callback | (1) token must equal `address(this)` or `WETH: flash mint only WETH10`; (2) `value <= 2^112-1` or `WETH: individual loan limit exceeded`; (3) unchecked `flashMinted += value`; (4) resulting value must be `<= 2^112-1` or `WETH: total loan limit exceeded`; (5) unchecked-credit receiver balance and emit `Transfer(0, receiver, value)`. |
| Callback | Typed zero-value call to `receiver.onFlashLoan(msg.sender, address(this), value, 0, data)` (`0x23e30c8b`). It observes incremented `flashMinted`, credited receiver balance, unchanged ETH, and the mint log. Child reverts bubble; no-code/short/malformed return decoding empty-reverts. A successfully decoded word unequal to `CALLBACK_SUCCESS` is replaced with exact `Error("WETH: flash loan failed")`. |
| Settlement after callback | Reads the **post-callback** `allowance[receiver][address(this)]`. If it is max uint256, skips allowance checks/write/log. Otherwise requires `allowed >= value` or `WETH: request exceeds allowance`, stores `allowed-value`, and emits `Approval(receiver, address(this), reduced)`. Then reads post-callback receiver balance, requires `balance >= value` or `WETH: burn amount exceeds balance`, debits it, emits `Transfer(receiver, 0, value)`, unchecked-subtracts `flashMinted -= value`, and returns `true`. |
| Event/rollback trace | Outer-frame WETH10 order is mint `Transfer`, arbitrary callback-log segment, optional finite-allowance `Approval`, burn `Transfer`: two or three WETH10-owned logs, plus any actual reentrant WETH10 or child logs. Any later failure rolls the entire nested transaction back. Nonzero entry value empty-reverts before guard (1). |
| Evidence owners | `DF-flash`; `TH-flash`, `TH-backed`, later settling/liveness families. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"flashMinted()","selector":"0x8b28d32f"} -->
### `flashMinted()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; output `uint256`; selector `0x8b28d32f`. |
| Success | Returns current flash-minted amount, including the reentrancy-visible temporary amount during a flash-loan callback. No effects. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. |
| Evidence owners | `DF-view`, `DF-flash`; `TH-read`, `TH-flash`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"maxFlashLoan(address)","selector":"0x613255ab"} -->
### `maxFlashLoan(address)`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; input `(token: address)`; output `uint256`; selector `0x613255ab`. |
| Success | If token is not `address(this)`, returns `0`. Otherwise returns unchecked `2^112-1 - flashMinted`; on reachable states the cap invariant prevents underflow. No effects. |
| Guards/reverts | No reverting source guard. Nonzero call value is an empty dispatcher revert. |
| Evidence owners | `DF-view`, `DF-flash`; `TH-read`, `TH-flash`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"name()","selector":"0x06fdde03"} -->
### `name()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; dynamic output `string`; selector `0x06fdde03`. |
| Success | Returns standard dynamic ABI encoding of `Wrapped Ether v10`; no effects. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. |
| Evidence owners | `DF-view`; `TH-read`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"nonces(address)","selector":"0x7ecebe00"} -->
### `nonces(address)`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; input `(owner: address)`; output `uint256`; selector `0x7ecebe00`. |
| Success | Returns the owner's current permit nonce; no effects. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. |
| Evidence owners | `DF-view`, `DF-permit`; `TH-read`, `TH-permit`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"permit(address,address,uint256,uint256,uint8,bytes32,bytes32)","selector":"0xd505accf"} -->
### `permit(address,address,uint256,uint256,uint8,bytes32,bytes32)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(owner, spender, value, deadline, v, r, s)` with address/uint256/uint8/bytes32 types; no outputs; selector `0xd505accf`. |
| Guard/digest order | (1) require `block.timestamp <= deadline` (equality succeeds) or exact `Error("WETH: Expired permit")`; (2) read `chainid()`; (3) form the Permit struct hash using the current `nonces[owner]` and post-increment that nonce unchecked; (4) use cached domain on the deployment chain, otherwise recompute it for current chain ID and `address(this)`; (5) call `ecrecover`; (6) require recovered signer is nonzero and equals owner or exact `Error("WETH: invalid permit")`. |
| Success/effects | Sets `allowance[owner][spender] = value`, emits `Approval(owner, spender, value)`, and returns empty data. Zero owner cannot pass the signer guard. Zero spender is accepted. |
| Rollback/quirks | An invalid signature tentatively increments the nonce before `ecrecover`, but the revert rolls that increment back. A valid call advances it exactly once modulo `2^256`. Forked-chain signatures use the recomputed current-chain domain. Nonzero entry value empty-reverts before the deadline guard. |
| Evidence owners | `DF-permit`; `TH-permit`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"symbol()","selector":"0x95d89b41"} -->
### `symbol()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; dynamic output `string`; selector `0x95d89b41`. |
| Success | Returns standard dynamic ABI encoding of `WETH10`; no effects. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. |
| Evidence owners | `DF-view`; `TH-read`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"totalSupply()","selector":"0x18160ddd"} -->
### `totalSupply()`

| Field | Frozen behavior |
|---|---|
| ABI | `view`, nonpayable; no inputs; output `uint256`; selector `0x18160ddd`. |
| Success | Returns unchecked `address(this).balance + flashMinted`, not the sum of booked balances. Force-sent ETH therefore increases the result; during flash callbacks the temporary minted amount also contributes. No effects. |
| Guards/reverts | No source guard. Nonzero value is an empty dispatcher revert. |
| Evidence owners | `DF-view`, force-send fixtures; `TH-read`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"transfer(address,uint256)","selector":"0xa9059cbb"} -->
### `transfer(address,uint256)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(to: address, value: uint256)`; output `bool`; selector `0xa9059cbb`. |
| Nonzero-recipient branch | For every `to != address(0)`, including `address(this)`, require caller balance `>= value` or exact `WETH: transfer amount exceeds balance`; debit caller, unchecked-credit `to`, emit `Transfer(msg.sender, to, value)`, return `true`. A self-transfer restores the same balance after the debit/credit but still emits. |
| Zero-recipient branch | Require caller balance `>= value` or exact `WETH: burn amount exceeds balance`; debit and emit `Transfer(msg.sender, 0, value)`; then low-level-call `msg.sender` with value `value` and empty calldata, forwarding ordinary remaining gas. The call observes the debit/log and reduced WETH ETH balance. Child revert bytes are not bubbled: any false call result is replaced by exact `WETH: ETH transfer failed`. Success returns `true`. |
| Rollback/entry | ETH-call failure rolls back debit and log. Nonzero entry value empty-reverts before either branch. |
| Evidence owners | `DF-state`, callback/reentrancy fixtures; `TH-state`, `TH-callback`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"transferAndCall(address,uint256,bytes)","selector":"0x4000aea0"} -->
### `transferAndCall(address,uint256,bytes)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(to: address, value: uint256, data: bytes)`; output `bool`; selector `0x4000aea0`. |
| Transfer phase | Executes exactly the two `transfer` branches above, including ordinary transfer to `address(this)`, branch-specific balance reasons, and for `to == 0` the ETH call to `msg.sender` with `WETH: ETH transfer failed` replacement. |
| Callback | After that phase succeeds, typed zero-value-call target `to` with `onTokenTransfer(msg.sender, value, data)`. It observes the completed transfer or withdrawal. Returns decoded Boolean verbatim, including `false`; child reverts bubble; codeless/zero target or bad return decoding empty-reverts and rolls back the entire preceding phase. Thus `to == 0` transiently burns and sends ETH to the caller, then the typed callback to zero empty-reverts everything. |
| Entry | Nonzero call value empty-reverts before the body. |
| Evidence owners | `DF-callback`; `TH-callback`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"transferFrom(address,address,uint256)","selector":"0x23b872dd"} -->
### `transferFrom(address,address,uint256)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(from: address, to: address, value: uint256)`; output `bool`; selector `0x23b872dd`. |
| Allowance phase | If `from == msg.sender`, bypass allowance entirely. Otherwise read `allowance[from][msg.sender]`; max uint256 bypasses check/write/log. A finite value must be `>= value` or exact `WETH: request exceeds allowance`, then is reduced and `Approval(from, msg.sender, reduced)` emitted. This phase precedes the balance guard, but a later revert rolls it back. |
| Nonzero-recipient branch | For every `to != 0`, including `address(this)`, require `balanceOf[from] >= value` or `WETH: transfer amount exceeds balance`; debit, unchecked-credit `to`, emit `Transfer(from, to, value)`, return `true`. |
| Zero-recipient branch | Require balance or `WETH: burn amount exceeds balance`; debit and emit `Transfer(from, 0, value)`; low-level-call **`msg.sender`** (not `from` or `to`) with `value` ETH and empty calldata. False call result becomes exact `WETH: ETH transfer failed`; success returns `true`. The callback observes any finite allowance reduction and burn. |
| Entry | Nonzero call value empty-reverts before allowance handling. |
| Evidence owners | `DF-state`, callback/reentrancy fixtures; `TH-state`, `TH-callback`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"withdraw(uint256)","selector":"0x2e1a7d4d"} -->
### `withdraw(uint256)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; input `(value: uint256)`; no outputs; selector `0x2e1a7d4d`. |
| Guard/effects | Require caller balance `>= value` or exact `WETH: burn amount exceeds balance`; debit and emit `Transfer(msg.sender, 0, value)`. |
| External call | Low-level call to `msg.sender` with `value` ETH and empty calldata after the debit/log. False result, regardless of child revert bytes, becomes exact `WETH: ETH transfer failed`; success returns empty data. Failure rolls everything back. |
| Entry/evidence | Nonzero entry value empty-reverts. Owners: `DF-state`, reentrancy fixtures; `TH-state`, `TH-callback`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"withdrawFrom(address,address,uint256)","selector":"0x9555a942"} -->
### `withdrawFrom(address,address,uint256)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(from: address, to: address payable, value: uint256)`; no outputs; selector `0x9555a942`. |
| Allowance phase | If `from == msg.sender`, bypass allowance. Otherwise max allowance bypasses check/write/log; a finite allowance must cover value or exact `WETH: request exceeds allowance`, then is reduced and emits `Approval(from, msg.sender, reduced)`. |
| Burn/call | Require post-allowance `balanceOf[from] >= value` or exact `WETH: burn amount exceeds balance`; debit and emit `Transfer(from, 0, value)`; low-level-call `to` with `value` ETH and empty calldata. False result is replaced by the uniquely spelled exact reason `WETH: Ether transfer failed`. The target observes finite allowance reduction, burn, and log prefix. |
| Rollback/entry | Any later failure rolls back allowance/balance/log/ETH effects. Nonzero entry value empty-reverts. |
| Evidence owners | `DF-state`, reentrancy fixtures; `TH-state`, `TH-callback`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"withdrawTo(address,uint256)","selector":"0x205c2878"} -->
### `withdrawTo(address,uint256)`

| Field | Frozen behavior |
|---|---|
| ABI | `nonpayable`; inputs `(to: address payable, value: uint256)`; no outputs; selector `0x205c2878`. |
| Guard/effects | Require caller balance `>= value` or exact `WETH: burn amount exceeds balance`; debit and emit `Transfer(msg.sender, 0, value)`. |
| External call | Low-level call to `to` with `value` ETH and empty calldata. False result is replaced by exact `WETH: ETH transfer failed`; success returns empty data. The target observes the debit/log. Failure rolls everything back. Address zero can succeed as an ETH target. |
| Entry/evidence | Nonzero entry value empty-reverts. Owners: `DF-state`, reentrancy fixtures; `TH-state`, `TH-callback`, `TH-backed`. Status: planned. |

<!-- WETH10-ENDPOINT {"signature":"receive","selector":null} -->
### `receive`

| Field | Frozen behavior |
|---|---|
| ABI | Payable empty-calldata receive; no selector, inputs, outputs, or return data. |
| Success/effects | Unchecked-credits `balanceOf[msg.sender] += msg.value` and emits `Transfer(0, msg.sender, msg.value)`. The contract balance already includes the incoming ETH. Zero value still follows the write/log path. |
| Dispatch | Only empty calldata selects receive. Nonempty unknown selectors do not fall through to it. No source guard or external call. |
| Evidence owners | `DF-state` plus dispatcher fixtures; `TH-state`, `TH-backed`. Status: planned. |

## Cross-cutting behavior

<!-- WETH10-CROSSCUT receive-vs-unknown -->
### Receive versus unknown selectors

Empty calldata always selects payable receive. Nonempty calldata whose first
four bytes do not identify one of the 27 generated selectors empty-reverts;
it is never treated as a deposit. The boundary contains exactly 27 functions
plus receive and no public Blanc helper.

<!-- WETH10-CROSSCUT nonpayability -->
### Nonpayability

Only receive, `deposit`, `depositTo`, and `depositToAndCall` accept call value.
Every other recognized selector with nonzero value is rejected by the compiler
dispatcher before source guards or effects, with empty revert data.

<!-- WETH10-CROSSCUT canonical-calldata -->
### Canonical calldata scope

Compatibility covers canonical ABI encodings, including canonical dynamic
offsets/tails and clean address words. Exact Solidity-decoder behavior for
truncation, dirty address words, pathological offsets, trailing shapes, and
other noncanonical inputs is not claimed. This exclusion does not relax the
known-selector/nonpayability dispatch rules or callback-return decoding.

<!-- WETH10-CROSSCUT staticcall -->
### STATICCALL behavior

The view endpoints perform no writes/logs/value calls and retain the endpoint
guard behavior above under a static context. Mutators are not promised to
produce one uniform error under `STATICCALL`: source guards execute in their
actual order until the first forbidden state-changing opcode. A failing guard
that precedes that opcode retains its exact WETH reason; otherwise the EVM
static violation empty-reverts. No write or log commits. Examples include
`flashLoan`'s token and individual-limit guards before its first write, and
balance/allowance guards that may win before a later write.

<!-- WETH10-CROSSCUT reentrancy-snapshots -->
### Reentrancy snapshots

Typed token callbacks occur after their initiating balance/allowance write and
log. Flash callbacks see incremented `flashMinted`, credited receiver balance,
and the mint log, and settlement reads post-callback allowance and balance.
ETH recipient callbacks occur after debit and burn log (and, where relevant,
after finite allowance reduction). Reentrant WETH10 calls are allowed; their
state and logs interleave at the actual call boundary. An outer revert rolls
back the full nested transaction.

<!-- WETH10-CROSSCUT force-sent-eth -->
### Force-sent ETH

ETH can arrive without receive/deposit and without a token credit. That surplus
is retained. `totalSupply` observes the contract ETH balance plus
`flashMinted`; the backing invariant is therefore an inequality, not equality.
No liveness promise says every booked balance is withdrawable under arbitrary
hostile callback/gas conditions.

<!-- WETH10-CROSSCUT gas-sensitive-callbacks -->
### Gas-sensitive callbacks

Adequate gas means each execution can reach the compared behavior. Low-level
ETH calls and typed callbacks use their actual remaining-gas behavior, but
Blanc need not match exact gas consumption, access lists, or callback-observed
`gasleft()`. Later gas claims measure Blanc's own compiled bytes only.

<!-- WETH10-CROSSCUT malformed-calldata-exclusion -->
### Malformed-calldata exclusion

Malformed **input** calldata is outside equivalence as stated above. Malformed
**callback return** data is inside: typed Boolean/bytes32 return decoding must
match the deployed decoder, including empty revert for codeless/short/invalid
encodings. Child revert returndata bubbles for typed callbacks, while a
successfully decoded wrong flash-loan magic word gets WETH10's replacement
reason.

<!-- WETH10-CROSSCUT delegatecall-exclusion -->
### Delegatecall exclusion

Using either runtime as a library through `DELEGATECALL` is outside the public
contract-boundary claim. Storage addresses, raw slots, `address(this)`, ETH
ownership, and immutable behavior in that context are not equated.

<!-- WETH10-CROSSCUT cryptographic-collision-scope -->
### Cryptographic collision scope

Balances, nonces, and `flashMinted` have structurally disjoint tagged Blanc
keys. Blanc allowance keys retain 254 low bits of the pair hash. Allowance
comparison is therefore indexed by the finite owner/spender pairs touched or
queried by a compared trace, with a local premise that distinct observed pairs
have distinct allowance keys. There is no global keccak-injectivity assumption
and no claim for adversarial cryptographic-collision states.

<!-- WETH10-CROSSCUT self-address-correspondence -->
### Self-address correspondence and DOMAIN_SEPARATOR worlds

Equivalence maps deployed `address(this)` to Blanc `address(this)` everywhere:
flash token checks/callback arguments, lender allowance, self recipients, log
emitter, and domain construction. Raw `DOMAIN_SEPARATOR` equality is valid in
exactly three worlds:

1. both contracts are at the literal mainnet target on chain ID 1;
2. on a non-1 chain, the locked reference takes its recomputation branch and
   both contracts use the same synthetic address; or
3. a freshly deployed/repatched reference has immutables for the same
   synthetic address and deployment chain as Blanc.

Otherwise compare the two domain formulas under address correspondence, not
raw cached words. Transplanting the literal locked mainnet runtime to a
synthetic address on chain ID 1 is invalid because its cached separator embeds
the original target address.

<!-- WETH10-CROSSCUT logical-state-projection -->
### Logical source-state to tagged-state projection

Source balances map by raw canonical address word; nonces map to high tag `01`;
allowances map to high tag `10` over the low 254 bits of the pair keccak; and
`flashMinted` maps to `B256.max` (tag `11`). ETH balance maps directly in the
world state. The projection is total for balances, nonces, `flashMinted`, and
ETH, and trace-local for allowances under the collision premise above. Raw
Solidity slots, storage roots/proofs, code/codehash, and source layout are not
compatibility surfaces.

## Deployment boundary

<!-- WETH10-DEPLOYMENT constructor -->

Deployment is separate from the 28 runtime endpoints. The constructor has zero
arguments, is nonpayable, and rejects nonzero endowment. It makes no external
calls and emits no logs. Logical balances, allowances, nonces, and
`flashMinted` start empty/zero. It reads the deployment `chainid()`, records it
as `deploymentChainId`, and computes the cached domain separator from that
chain ID and the new contract's own address. Compatibility requires this
generic fresh-deployment behavior, not source initcode bytes, CREATE2 address,
deployment gas, or literal installed-runtime transplantation. Evidence owners:
planned deployment fixtures and the later initcode/runtime theorem family.
