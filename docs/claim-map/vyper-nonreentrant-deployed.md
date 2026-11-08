# Deployed-bytecode claim map: Vyper V+ and V−

## 5.5 Vyper V+: guarded-body reentrancy exclusion

The fixed implementation 0x847e, called directly or through the ETH/stETH
proxy.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| In any execution (any outcome, `Exec 0 …`), while an owner frame is inside one of the mutating guarded bodies and has not released, no descendant enters any guarded body for that owner | generic `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:128`); instances `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_impl` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:142`), `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_exclusion_stethPool` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean:161`) | Message (all outcomes) / temporal exclusion | CODE (implementation or proxy bytes, `hP`, `hI`); ENV well-formed root `hroot`; **HASH-T** `HashAvoidIn` (executed Keccak digests differ from lock slot 0) || In a pc-0 frame running the 0x847e code (covered fork, `HashAvoid 0`), every node executes only `CALL` or `STATICCALL` among external calls and never `DELEGATECALL`, `CALLCODE`, `CREATE`, `CREATE2` or `SELFDESTRUCT` [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.lock_no_forbidden` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/LockDominance.lean:44`)] |
| The same for a transaction's retained top-level execution, with `hroot` **derived** (`prepareMessage` builds the root from the debited world) | `Blanc.ExecutionTrace.TransactionTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:251`); message carriers `Blanc.ExecutionTrace.ProcessMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:70`), `Blanc.ExecutionTrace.ProcessCreateMessageTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:116`), `Blanc.ExecutionTrace.MessageCallTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:180`) | Transaction / temporal exclusion | `hfork`, `hP`, `hI` on the opening state; `tx.auths = []` (EIP-7702 excluded); `HashAvoidIn` of the retained execution | |
| The same for every raw frame root of a configured history; pc 0 and the covered fork are derived | `Blanc.ExecutionTrace.ConfiguredHistoryTrace.vplus` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:283`) [roots by `Blanc.ExecutionTrace.MessageCallTrace.rootEntry` (`Blanc/ExecutionTraceEntry.lean:58`)] | History / temporal exclusion | per retained execution `R`: `hP`, `hI`, `hroot`, `HashAvoidIn` (not derivable from the trace) | statement form `VplusExcludes` [`Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`); `Blanc.Lift.VyperNonreentrantDeployed.Fixed.vplus_excludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:50`)] |
| **Nonvacuity (proxy-free):** an actual Jaune execution of the deployed 0x847e runtime in which a mutating guarded body (`remove_liquidity`, body start 0x1bae) is active and spawns a STATICCALL (pc 0x337a) to a coin, whose read-only reentry into the guarded view `get_virtual_price()` **reverts at the lock check** and never reaches a guarded body. It carries the full antecedent of `vplus_exclusion_impl` and its conclusion | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_witness_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:251`) (quantified over `g` with `CoveredFork g`, Prague included); every derivation of the entered machine, under any covered fork: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.vplus_run_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean:82`) | Message / closed witness | none (closed) | Kernel-checked; every walk boundary matches an EELS Prague trace (the printer is untrusted). No KECCAK executes, so `HashAvoidIn` holds by "no hash executed" |
| **Nonvacuity (proxy instance, mutating reentry):** an execution entered through the 45-byte forwarder 0x21e2… (DELEGATECALL to 0x847e). `remove_liquidity` holds the lock and CALLs a synthetic receiver with 100 wei; the receiver calls back through the forwarder with `add_liquidity`'s selector (mutating, guarded); the comparator frame reverts at the lock check (pc 0x53 → 0x477e, no guarded body start); the receiver stops; the outer call **succeeds** and the pool balance goes from 1000 to 900 wei. This is a witness of `vplus_exclusion_stethPool` (the covered form carries that theorem's premises and antecedent, and the reentry conclusion `¬ lockL.Enters`) | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_witness2_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:227`) (every covered fork); every derivation: `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.vplus_run2_at` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Top.lean:104`) | Message / closed witness | none (closed) | `HashAvoidIn` by digests: the one KECCAK256 leaves a digest different from slot 0 (control `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.hashControl_bites` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness2/Run.lean:413`); engine control `Blanc.Lift.NodeWalk.hashPol_bites` (`Blanc/Lift/NodeWalk.lean:1086`)) |
| **The headline:** on every covered fork, the eight setup messages, folded from the creator-only world, reach a world whose LP ledger is sound at 2000, and the exit message `remove_liquidity(200, [0, 0], receiver)` then settles to a world whose ledger is sound at 1800, with the receiver paid 100 wei and its guarded reentry refused at the shared lock: while the pool frame holds the lock it pays the receiver, and the receiver's guarded call back into the pool reverts without entering a guarded body. Intermediate, the detailed capstone: **Nonvacuity reachable from deployment and initialization (message level):** on every covered fork, nine messages run in sequence from a world holding only a funded, code-free creator, each from the previous settled world and each settling without error: the preserved 0x847e implementation creation input (placed at its registered address by a supplied CREATE target), a labelled synthetic EIP-1167 clone creation, `initialize` and `set_oracle(0, 0)` through the clone, synthetic token and receiver creations, `approve`, `add_liquidity([1000, 1000], 0)` with 1000 wei, then `remove_liquidity(200, [0, 0], receiver)`. Before the last message the LP ledger is sound over its single holder (`totalSupply = balanceOf[creator] = 2000`). While the pool frame holds the shared lock it sends the receiver 100 wei; the receiver calls the guarded, mutating `add_liquidity` through the clone; that pool frame reads the held lock and reverts without reaching a guarded body, and the receiver returns normally. The outer call commits: the receiver holds 100 wei and 100 tokens; supply and the creator's LP balance are 1800 | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_exit` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean:153`) over the message fold `Blanc.Lift.runMessages` (`Blanc/Lift/RootMessages.lean:41`), with `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.ReentryRefused` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean:135`); via `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_reachable_capstone` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean:48`); the instantiation, with the receiver and forwarder code facts, `Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.vplus_reach_exit` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Main.lean:60`) | Message / closed witness | none (closed) | The headline states the ledger outcome and the refused reentry; the capstone keeps every frame fact. `vplus_exclusion` instantiated for this execution with its fork, code, root and trace-local `HashAvoidIn` premises proved. Synthetic token, receiver and clone code; supplied CREATE targets; calls use chain id 1 and block time 1,700,000,000; no historical inclusion; no transaction admission |

**Fork coverage.** The exclusion assumes `CoveredFork`; both witnesses are
stated for every fork in Prague, Osaka, BPO1 and BPO2 (the Prague kernel facts
are transported by `Blanc/ForkUniform.lean`, `Blanc/Lift/NodeWalkFork.lean` and
`Blanc/Lift/WitnessFork.lean`; the runs execute no CLZ, read no blob price, and
enter no MODEXP or P256VERIFY). The reachable witness
`vplus_reachable_capstone` is likewise stated for every covered fork.

**Non-claims.** Unguarded functions; reentry after release; mutation while
only a view is running; pricing, LP economics, liveness; EIP-7702-delegated
roots (excluded from the transaction and message carriers); a validated
transaction reaching the witness state; historical prestates (the closed
witnesses' prestates are synthetic; the reachable witness's prestate is reached
by executed messages from a synthetic creator-only world; the reader and
receiver are synthetic).

## 5.6 Vyper V−: cross-function reentrancy corrupts the LP ledger

The vulnerable implementation 0x6326, called through its proxy.

| Claim | Theorem | Level / kind | Premises | Notes |
|---|---|---|---|---|
| **The headline:** on every covered fork, the seven setup messages, folded from the creator-only world, reach a world whose LP ledger is sound (supply and the attacker's LP balance both 2000), and the attack message then settles to a world whose ledger is broken (supply 1800, the attacker's LP balance 1906). Intermediate, the detailed capstone: **Violation reachable from deployment and initialization (message level):** on every covered fork, eight messages run in sequence from a world holding only a funded, code-free creator, each from the previous settled world and each settling without error: the preserved 0x6326 implementation creation input (placed at its registered address by a supplied CREATE target), a labelled synthetic clone creation, `initialize` through the clone (`A = 100`, fee 0), synthetic token and attacker creations, `approve`, `add_liquidity([1000, 1000], 0, attacker)` with 1000 wei, then the violating call. After the seventh message the LP ledger is sound over its single holder (`totalSupply = balanceOf[attacker] = 2000`) and all nonzero pool storage lies in a listed slot set. In the eighth, the creator calls the attacker contract, which calls `remove_liquidity(200, [0, 0], attacker)`; holding lock slot 2, the pool sends the attacker 100 wei; the callback calls `add_liquidity([100, 0], 0, attacker)` through the same clone, which takes lock slot 0 and succeeds. The message settles with `totalSupply = 1800 < 1906 = balanceOf[attacker]`, compared as natural numbers. The universal form states the same message and conclusions for every world agreeing with the reached world on the 14 storage slots and 6 accounts the violation reads (`Checkpoint`) | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_attack` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:78`) over the message fold `Blanc.Lift.runMessages` (`Blanc/Lift/RootMessages.lean:41`), with `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.LedgerBroken` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:68`); via `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_reachable_capstone` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:39`); universal form `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol.vminus_reach_violation` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean:35`) | Message / closed witness (capstone); message / universal over `Checkpoint` worlds | none for the capstone; `Checkpoint W` for the universal form | The headline states the ledger outcome; the reentry frame chain is in `vminus_reach_violation`. Synthetic token, attacker and clone code; supplied CREATE targets; default block environment. **This row and the transaction row below concern different worlds (different proxy, attacker, sender and token addresses); neither implies or extends the other. The equal figures come from the same scenario amounts, not a shared state** |
| Message level: a successful message execution in which `remove_liquidity` holds lock slot 2, its ETH callback reenters `add_liquidity` (lock slot 0) through the proxy, and the final ledger has `totalSupply = 1800 < 1906 = balanceOf[attacker]`. The two guards are on different slots (bytes 6900-6911 versus 88-99) | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top.vminus_witness` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Top.lean:155`); all covered forks `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top.vminus_witness_covered` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/ForkTop.lean:159`) | Message / closed witness | none (closed) | synthetic prestate (Section 7); stated for Prague, other covered forks by transport |
| **Transaction level, all covered forks:** conditional on block room, Jaune's `processTransaction` accepts a fixed signed type-2 transaction (zero fee and value, 16,043,200 gas, below 2^24, an access list of 19 addresses), and the returned world has `totalSupply = 1800 < 1906` in the pool | `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_process` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxC/Envelope.lean:136`); closed message part `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.vminus_txC_message` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxC/Closed.lean:49`) (gas 15,822,837 left, refund 42,600, `accountsToDelete` empty) | Transaction / conditional witness | block room `hroom` | every other admission check, including signature recovery (`Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.txC_recoveredSender` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxCRecover.lean:99`)), is kernel-evaluated on the concrete transaction and block. From the synthetic prestate of Section 7 (proxy 0x9848…85c5 with seeded storage, attacker 0xaaaa…a2a2); not the deployment-reached world of the first row, and `vminus_reach_violation` does not cover it |

**Fork coverage.** `vminus_witness_covered`, `vminus_txC_message` and
`vminus_txC_process` quantify `g` with `CoveredFork g`. A Prague-only message
form, `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.vminus_tx_message` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Tx/Closed.lean:26`), carries 30,021,064 gas, which is above
the EIP-7825 cap from Osaka on and so is not a valid transaction there; cite
the `TxC` forms. The reachable forms `vminus_reachable_capstone` and
`vminus_reach_violation` also quantify over every covered fork.

**Non-claims.** For the closed message witness and the transaction rows: a
reachable or historical prestate. For every row: a historical prestate, and a
transaction reaching the reachable row's checkpoint; a real historical
attack; a signature-generic transaction (the signature, transaction hash,
index 0 and coinbase are fixed); the attacker model is synthetic (Section 7).

## Artifacts

| Contract | Address | Runtime bytes | keccak256 codehash | Creation transaction | Block |
|---|---|---:|---|---|---:|
| Vyper pool implementation, fixed (V+) | 0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9 | 18,320 | 0x59469db6b75b045025abb5386ae6b7ef7e1698d13ee93f3d4ed32d5f72506e0e | 0xfaad66f8fa2b4883b9e5c91b69e31ac8c2cdbc6d383b8776d0eee94d3ee0a251 | 17,110,099 |
| ETH/stETH pool proxy to the V+ implementation | 0x21e27a5e5513d6e65c4f830167390997aa84843a | 45 | 0x9e28a09452d2354fc4e15e3244dde27cbc4d52f12a10b91f2ca755b672bfa9be | not recorded | not recorded |
| Vyper pool implementation, vulnerable (V−) | 0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e | 17,535 | 0xba0284a6a8a86734c1c777e3c6b5b56f2c8ba95dc0f7eba481c6d09da7885ebc | 0xd27491757b3a4bc9287ed44ce5c43de9f32131264548ce139f0a702c3d5f389e | 12,904,329 |
| Pool proxy to the V− implementation | 0x9848482da3ee3076165ce6497eda906e66bb85c5 | 45 | 0xbed04db3507e08e5220f6eadf98d5df05bdbc74df129c73fcbab7c441e86b124 | not recorded | not recorded |

**Synthetic fixtures** (not deployed artifacts): for V−, an attacker (85
bytes), a dispatcher attacker (186 bytes) and a coin (30 bytes); for V+, a
reader (41 bytes) and a receiver (86 bytes). The reachable witnesses of Sections
5.5 and 5.6 use their own fixtures, each installed by an executed CREATE of its
registered creation input: a shared address-keyed token Token20 (299-byte
runtime, 315-byte creation input), the V− attacker AttackerR (186-byte runtime,
different code from the dispatcher attacker; 195-byte creation input), the V+
receiver ReceiverR (89-byte runtime; 98-byte creation input), and one 54-byte
synthetic EIP-1167 clone-creation input per side. The two implementations are
created there from their preserved creation inputs,
`scripts/lift/inputs/vyper-847e-creation.hex` (18,353 bytes) and
`scripts/lift/inputs/vyper-6326-creation.hex` (17,569 bytes), whose origin is
recorded in the certificate provenance; that is not historical inclusion.

## Trust base

| Component | What is trusted | Evidence |
|---|---|---|
| Signature recovery | Premise of the signature-generic transaction theorems | `recoverSender … = .ok E` is a premise of every theorem that quantifies over all signed transactions, since there is then no single signature to evaluate. For a concrete transaction the kernel evaluates recovery: `Blanc.Lift.WithdrawalRequest.FloodTx.txB_recoveredSender` (`Blanc/Lift/WithdrawalRequest/FloodTxRecover.lean:149`) and, for V−, `Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.txC_recoveredSender` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/TxCRecover.lean:99`) |

## Summary matrix

| | M1 | M2 | M3 | M4 | M5 | M6 | M7 | M8 |
|---|---|---|---|---|---|---|---|---|
| V+ | ✓ | ~ [j] | ~ [j] | ✓ HASH-T (per execution) | ✓ [q] (message level; the exclusion itself takes no INIT premise) | ✓ nonvacuity (witnesses), and a reachable witness [q] | ~ [k] | ✓ |
| V− | ✓ | — | — | — | ✓ [q] (message level) | ✓ [q] violation at a reachable state | ✓ [l] | ✓ |

[j] Message, transaction
and history corollaries exist; per retained execution the world premises `hP`
and `hI`, the root code identity and `HashAvoidIn` are not derivable from the
trace (the transaction form derives `hroot`).

[k] A transaction form exists
for the exclusion; no admitted transaction *witness* reaches an active guarded
body.

[l] A fixed signed transaction; its signature recovery is a kernel theorem (`txC_recoveredSender`).

[q] Deployment, initialization and liquidity are executed messages
from a creator-only world, not admitted transactions (§7 item 3 applies); the
V− transaction row (M7) starts from a different, synthetic prestate. For both V+ and V−, M5 records the executed setup of the reachable witness; the older witnesses keep their synthetic prestates.

## Disclosures and limits

5. **Witness-engine guard.** The V− interpreter engine refuses synchronous
   MODEXP (0x05) and P256VERIFY (0x100) child frames
   [`Blanc.Lift.Witness.frameEntryForkFree` (`Blanc/Lift/WitnessArms.lean:1056`), used by `Blanc.Lift.Witness.callStep` (`Blanc/Lift/WitnessArms.lean:1065`)]. The `wrun … = .cont`
   run conjuncts of `vminus_witness` therefore also mean that the run enters no
   MODEXP or P-256 frame; that is what makes the runs fork-uniform. The V+ walks
   expose spawns as explicit nodes and execute no CLZ and no MODEXP or
   P256VERIFY.

6. **The following witness and deployment forms cover Prague, Osaka,
   BPO1 and BPO2:** the listed V± message witnesses are closed;
   `vminus_txC_message` is closed, while `vminus_txC_process` requires
   block room; the reachable capstones are closed, while
   `vminus_reach_violation` takes `Checkpoint W`. The forms are
   `vplus_witness_covered`, `vplus_witness2_covered`, `vminus_witness_covered`,
   `vminus_txC_{message,process}`, `vplus_exit`, `vminus_attack`, `vplus_reachable_capstone`,
   `vminus_reachable_capstone`, `vminus_reach_violation`,
   `curve_deploy_covered`.

7. **Synthetic prestates and fixtures (V±).** For the closed witnesses: pool
   storage (lock slots, balances, totalSupply), ETH balances, and the reader,
   receiver, attacker, dispatcher-attacker and coin contracts are synthetic. The
   reachable V± witnesses instead reach their pool storage by executed messages
   from a creator-only world (§5.5, §5.6); their token and receiver/attacker
   code and their clone-creation inputs remain synthetic, although the 45-byte
   forwarder runtime each clone creation installs is byte-identical to the mainnet
   forwarders' code (the stETH-ng pool's for V+; the pETH/ETH, msETH/ETH and
   alETH/ETH pools' for V−). The coin-1 contract in
   V+ witness 2 is the receiver itself. The synthetic attacker and coin bytes
   are registered certificates, not deployed artifacts.

8. **Fixed signed transactions.** `vminus_txC_process` (and the Prague-only
   `Tx.vminus_tx_message`) is about one fixed signed transaction: signature
   `(r,s)`, transaction hash, index 0, **coinbase = the sender E** (warm, so
   address-shadow literals hold), chain id 0, base fee 0, block gas limit
   60,000,000. A signature-generic form is not built. The transaction's
   signature recovery is a kernel theorem (`txC_recoveredSender`). The
   signature of the Prague-only `Tx` transaction `tx0` is checked only by an
   interpreter `#guard`, not a kernel fact; no theorem cited here depends on it.

25. **The reachable V± witnesses are message level.** They do not model the
    transaction and block effects around a message: sender nonce increments and
    nonce-derived creation addresses, intrinsic gas, fees and refunds, the
    coinbase payment, warm sets (an admitted transaction warms its sender, its
    target and the precompiles; these messages start from empty access sets),
    block-level system calls, withdrawals and EIP-7702 delegations. Some of these
    run code: a block's system calls execute messages that write their system
    contracts' storage (EIP-4788's beacon-roots contract, for example). None of
    them is addressed to the pool, token or attacker contracts of these
    witnesses, but no theorem proves that their slots are preserved, and changed
    balances, gas or warm sets could change later execution. The implementation
    addresses are supplied `CREATE` targets, not the nonce-derived addresses of
    the creator, whose nonce stays zero. That equivalent messages are producible
    by admitted transactions (sender keys, nonce-derived addresses, gas and warm
    sets) is argued, not proved.

## Named premises and definitions

| Name | Declaration | Role |
|---|---|---|
| `VplusExcludes` | `Blanc.Lift.VyperNonreentrantDeployed.Fixed.VplusExcludes` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean:44`) | the statement form of the V+ exclusion |

## Uses of the shared API

### From `docs/COMMON_API.md`: E5. I need to inspect what happened in an `Exec`

Worked examples: `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean` (a read-only
  spawn) and `.../Fixed/Witness2/{Run,Frames,Top}.lean` (an ETH-paying body, a nested reentry
  through an EIP-1167 forwarder, a committing run).

Generalize the run lemma over
  `S = e0.sta.withFork g` and derive the fixed-fork statement at Prague; worked examples
  `vplus_run_at`/`vplus_witness_covered` in
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean` (one nesting level) and
  `vplus_run2_at`/`vplus_witness2_covered` in `.../Fixed/Witness2/{Frames,Top}.lean` (the
  frame lemmas take the fork, six spawns of all three call kinds).

Worked example: the
  identity-precompile copy of `initialize` in
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Init/{Run,Top}.lean`.

Worked use: `forwarder_root_re`/`leaf_root_re` and the frames of
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Fund/{Root,Add}.lean` and `.../Fixed/Exit/`.

Restate each frame lemma for the machines
  `X.withFork g`, taking the Prague kernel fact and the spawn facts (`callPrep_withFork`,
  `frameEnterS_withFork_of_stat`, a kernel fact on the spawned frame's `codeAddress`); worked
  example `vminus_witness_covered` in
  `Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/{ForkKernel,ForkFrames,ForkTop}.lean`.

Worked example
  `Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/{TxTopC,TxC/*}.lean`
  (`vminus_txC_message`, `vminus_txC_process`: a 16,043,200-gas transaction, one kernel run of the
  Prague chain, every frame lemma restated for `withFork g`).
  Its signature premise is discharged for the concrete transaction by `TxC.txC_recoveredSender`
  (`TxCRecover.lean`): the access-list encoding by `toBLT_noKeys`/`join_entries`, the signing hash and
  secp256k1 recovery by `decide +kernel` (the kernel cannot unfold `BLT.toBytes`, so rewrite the encoding first).

worked use:
  `init_run`/`oracle_run` in `.../Fixed/Init/{Top,OracleTop}.lean`

worked use: `approve_run`/`add_run` in `.../Fixed/Fund/{Approve,Add}.lean`.

worked use: `frameB_at` in `.../Vulnerable/Reach/AddTop.lean`

worked use:
  `e2StaticFacts` in `.../Vulnerable/Reach/ViolRootRun.lean`

worked use:
  `e4T_meta` in `.../Vulnerable/Tx/Entry.lean`

worked use: `origAgreeOn_O0` in `.../Vulnerable/Reach/ViolBoundary.lean`

### From `docs/COMMON_API.md`: T3. The wrapper is a transaction and the fact is about an installed contract

Worked use:
`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Tx/Envelope.lean`.

### From `docs/COMMON_API.md`: C2. I need deployment/message correspondence

Worked uses: `vminus_attack` (`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Reach/ViolFinal.lean`)
  and `vplus_exit` (`Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exit/Capstone.lean`).

### From `docs/COMMON_API.md`: C9.2. I need to connect a real execution with a lifted run

Worked use:
  `Blanc/Lift/VyperNonreentrantDeployed/Concrete/ProxyConcrete.lean`.

Worked use:
  `Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Top.lean` (`vminus_witness`).

### From `docs/COMMON_API.md`: C9.6. I need the calls, child frames and logs of a lifted frame

Worked use:
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/LockDominance.lean`; the full
  `lock_exclusion` instance (dominance, `ownerDiscipline_of_world` for a
  forwarder owner, `NoDelegateFrom` from the cursor, release-pc activity) is
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean`; its transaction
  and history forms (`vplus_excludes`, `TransactionTrace.vplus`,
  `ConfiguredHistoryTrace.vplus`: the well-formed-root premise derived from the
  prepared message, every raw root of a history covered) are
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean`.

### From `docs/COMMON_API.md`: C9.11. I need deployment, CREATE, CREATE2 or a clone

worked use: `Lift/VyperNonreentrantDeployed/Vulnerable/Reach/Deploy.lean`

## See also

- [Disclosures and limits: item 3](curve-3crv.md#disclosures-and-limits)
