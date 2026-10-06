# Uniswap V2 Pair functional model: different-family (Claude) review

- Episode: uv2nh-model-review-1
- Goal: uniswap-v2-pair-bytecode-v1 (U2 correspondence table plus cross-family review; U3/U4/U5/U7 statements)
- Reviewer model: Claude Opus 5.5 (claude-opus-5-5). The author (Codex Sol, GPT) and the earlier reviewer (Astra, GPT) are from a different family, so this review meets the cross-family requirement.
- Model snapshot reviewed: `~/blanc/.worktrees/uv2nh-review`, detached at **2ab4868c**. Model.lean, Execution.lean, Consumption.lean, AMMArithmetic.lean, BabylonianSqrt.lean, Properties.lean, PropertiesOracle.lean and PropertiesSwap.lean are byte-identical in the live lane `uniswap-v2-newhost` HEAD **009d191a**. PropertiesLedger.lean exists only in the lane (commit 91377037, blob ca2aea11) and was reviewed there.
- Source: Uniswap/v2-core v1.0.1 at the scratchpad copy. sha256: UniswapV2Pair.sol 43a5421b…cbd, UniswapV2ERC20.sol b8ce8892…be32, Math.sol e4a9d451…325f, SafeMath.sol 4b1c95ff…16ae, UQ112x112.sol 6633b57b…db.
- Method: read-only. No builds, no Lean MCP, no holds. Every claim below comes from reading the source text. Where a claim depends on solc 0.5.16 code-generation behaviour, the report says so; the bytecode refinement (U2a) is what settles it.

Paths: `M` = Blanc/Lift/UniswapV2Pair/Model.lean, `X` = Execution.lean, `P` = UniswapV2Pair.sol, `E` = UniswapV2ERC20.sol.

## Status at the integrated checkpoint

This register keeps the review as it was written: the cross-family source-versus-model
correspondence review that the goal requires. Its model and `file:line` citations are those of
the snapshot it reviewed, not of this checkpoint, and its table and notes were not re-verified
here. What changed since, checked against this tree:

- **S1 (oracle law at run level): closed.** `OracleUpdate.Lawful`, `State.update_oracle_lawful`
  and `runTyped_oracle_law` (`Blanc/Lift/UniswapV2Pair/PropertiesOracleLaw.lean`) state the
  wrapped `Δt`, the increments and the timestamp chain through the driver;
  `OracleControls.oracle_law_requires_timestamp_wrap` is the control.
- **S2 (swap balances not identified): closed in the form the review proposed.**
  `runTyped_swap_success_reserves` concludes that the final reserves equal the answers.
- **S3 (later mint, burn payout, callback at run level): closed.** `runTyped_mint_later`,
  `runTyped_burn_payout` and `runTyped_swap_callback_request`.
- **S4 (burn's NoShrink is not the literal NoShrink): disclosed.** The exact per-entry forms are in
  `docs/DEPLOYED_BYTECODE_CLAIM_MAP.md` section 5.8 and section 7 item 17.
- **S5 (the U7 model control is not the storage-key control): a storage-level control now
  exists,** `LedgerKeyControl.approve_storage_alias_breaks_ledger`, conditional on the alias
  hypothesis; `footprintSum_dup_breaks_ledger` remains the model control.
- **S6 (the rounding control is a seam witness): replaced by mutated drivers.**
  `ModelMutants` clones only the driver pieces that call the changed arithmetic;
  `ModelControls.mintRoundUp_breaks_feeOff_product` fails the product inequality on a state the
  mutant reaches. The frame-level burn-rounding control
  (`RefinementControls.burn_refinement_control`) is still conditional on two named hypotheses.

## 1. Correspondence table

| Source (file:line) | Model (file:line) | Verdict |
|---|---|---|
| E:9-11 `name`, `symbol`, `decimals` constants | X:27-29 `getterResult` `.name/.symbol/.decimals` ("Uniswap V2", "UNI-V2" bytes checked, 18) | exact (ABI string image X:21-23) |
| E:12 `totalSupply` getter | X:32 | exact |
| E:13 `balanceOf(address)` getter | X:33 | exact |
| E:14 `allowance(address,address)` getter | X:34 | exact |
| E:16 `DOMAIN_SEPARATOR` getter | X:35 | exact |
| E:18 `PERMIT_TYPEHASH` getter | X:15-16, X:31 | exact (constant matches E:18 literally) |
| E:19 `nonces(address)` getter | X:36 | exact |
| E:24-38 ERC20 constructor (DOMAIN_SEPARATOR = keccak(abi.encode(typehash, keccak(name), keccak("1"), chainid, this))) | M:93-98 `State.empty factory domain` | deviation: `domain` is a free parameter. The EIP-712 domain hash is not computed in the model; U8 must supply it (outside this model review) |
| P:30 `unlocked = 1` initializer | M:98 `unlocked := 1` | exact |
| P:61-63 Pair constructor `factory = msg.sender` | M:93-95 `factory` parameter | deviation in the same way: parameter; binding to the sender is U8's job |
| E:40-44 `_mint` (add on totalSupply, then add on balanceOf[to], Transfer(0,to,v)) | M:101-107 `mintLP` | exact. Both overflow checks read the pre-state; the slots are distinct, so the sequential reads agree |
| E:46-50 `_burn` (sub on balanceOf[from], then sub on totalSupply, Transfer(from,0,v)) | M:110-116 `burnLP` | exact (same revert string for both checks) |
| E:52-55 `_approve` | M:131-134 `approveLP` | exact; static write fault modelled |
| E:57-61 `_transfer` (sub then add on the debited map, so self-transfer is exact) | M:119-129 `transferLP` | exact. Order: underflow guard, then static fault (the first SSTORE), then add-overflow on the debited map |
| E:63-66 `approve` returns true | X:247-248 | exact (`encodeWords [1]`) |
| E:68-71 `transfer` returns true | X:249-250 | exact |
| E:73-79 `transferFrom` (max-allowance skip; otherwise sub then store; no Approval event) | M:137-145, X:251-252 | exact. B256.max = 2^256-1 (Jaune/Basic.lean:93). Static fault comes after the allowance sub-check, as the SSTORE order requires |
| E:81-93 `permit` | X:315-324 (deadline, static, nonce++, digest, suspend to precompile 1) + X:564-567 (recovered ≠ 0 ∧ = owner, `_approve`) + X:286-289 `permitDigest` | exact at the typed level: `deadline >= block.timestamp` ↔ `ctx.timestamp ≤ deadline`; old nonce in the digest, wrapping `nonce + 1`; `0x1901 ‖ DOMAIN_SEPARATOR ‖ keccak(abi.encode(typehash, owner, spender, value, nonce, deadline))`; not locked. ECRECOVER output memory is abstracted to `ExternalResult.recoveryOutput` (X:84, X:397); see finding N3 |
| P:15 `MINIMUM_LIQUIDITY` getter | X:30, X:449 (`mintLP 0 1000`), M:213 | exact |
| P:16 `SELECTOR` (transfer) | X:267-268 `0xa9059cbb` | exact |
| P:18-20 `factory`, `token0`, `token1` getters | X:37-39 | exact |
| P:22-24, 38-42 `getReserves` | X:40-41 | exact (three words: r0, r1, blockTimestampLast) |
| P:26-28 `price0CumulativeLast`, `price1CumulativeLast`, `kLast` getters | X:42-44 | exact |
| P:31-36 `lock` modifier (require unlocked==1; unlocked=0; body; unlocked=1) | X:298-303 `Frame.lock`, X:403-405 `finishLocked`; applied at X:325-328 to mint, burn, swap, skim, sync only | exact. The LOCKED guard comes before the static fault (SLOAD then SSTORE). permit, initialize and the ERC-20 entries are unlocked, as in the source |
| P:44-47 `_safeTransfer` (low-level call, no extcodesize; success ∧ (len==0 ∨ decode bool)) | X:264-283 (`requiresCode := false` for transfer), X:379-386 | exact on the typed level: len 0 → ok; len ≥ 32 → first word ≠ 0; 0<len<32 → empty revert (ABI decoder V1 short-input revert, codegen-dependent); !success → TRANSFER_FAILED |
| P:49-59 events Mint/Burn/Swap/Sync | M:73-80 | exact field order. `Sync` carries the post-write reserves, which equal the guarded balances |
| P:66-70 `initialize` (FORBIDDEN, then two SSTOREs; no lock, no event, empty return) | X:253-259 | exact; the sender check comes before the static fault |
| P:73-86 `_update` | M:148-170 `State.update`, X:407-420 `finishUpdated` | exact: `<= uint112(-1)` ↔ `< 2^112`; `ts = timestamp % 2^32`; `dt` wraps mod 2^32; increments `⌊r1·2^112/r0⌋·dt` (no wrap possible: < 2^224·2^32); `+=` modular via B256 addition; reserves and timestamp written; Sync emitted. Uses the *cached* reserves (P:73 args) and the *storage* blockTimestampLast, as in the source |
| P:89-107 `_mintFee` | M:182-205 `mintFee` | exact on state. feeTo==0 sets kLast := 0 unconditionally, where the source writes only if kLast ≠ 0: same post-state, gas-only difference (the U6 gas proof must use the source shape). rootK, rootKLast via `Nat.sqrt`, linked to Math.sqrt by BabylonianSqrt.lean:106 `sourceResult_eq_sqrt` over the full Nat domain and :189 `body_bounds` (no wrap in `y/x + x`). The SafeMath checks are kept in source order (mul, mul, add); the rootK*5 and denominator checks can never fire but are harmless. kLast is read *after* the feeTo STATICCALL, as at P:90-92 |
| P:110-131 `mint` | X:332-334, X:492-506, X:441-462, X:407-420 | exact: lock; cached reserves; balanceOf token0, then token1 (token1 read from storage at resume, as in source); both `sub` checks after both reads; feeTo STATICCALL; `_mintFee`; totalSupply after fee; first-mint `sqrt(a0·a1) − 1000` with mul and sub checks, then `_mint(0,1000)`, then require liquidity>0, then `_mint(to)`; `_update`; `kLast := reserve0·reserve1` from the *updated* state iff feeOn; Mint(sender,a0,a1); returns liquidity. Event order: fee Transfer, Transfer(0,0,1000), Transfer(0,to,L), Sync, Mint |
| P:123 `Math.min(a0·T/r0, a1·T/r1)` | M:216-223, AMMArithmetic.lean:14-15 | exact, including the left-to-right order: mul0, div0, mul1, div1. Division by zero is a separate `divisionByZero` failure (0.5.16 emits INVALID) |
| P:134-156 `burn` | X:335-339, X:507-531, X:464-479 | exact: tokens cached in locals at entry; liquidity = balanceOf[this] read after both balance calls; fee; `L·b/T` floored, with checks in source order; require both >0; `_burn(this,L)`; transfer0, transfer1; re-read balances; `_update(cached reserves)`; kLast iff feeOn; Burn(sender,a0,a1,to); returns (a0,a1) |
| P:159-187 `swap` | X:340-360, X:422-435, X:532-546, M:236-259 | exact: lock, then OUTPUT, LIQUIDITY, INVALID_TO in source order; transfer0 iff out0>0; transfer1 iff out1>0; callback iff data nonempty (high-level call: `requiresCode := true`, CALL kind, calldata `0x10d1e85c ‖ sender, out0, out1, 0x80, len ‖ data ‖ pad`); balances after callback; `amountIn = b − (r − out)` with Nat truncation = the source ternary; INPUT; SafeMath checks; K over the post-callback balances; `_update`; Swap event after Sync; empty return; kLast untouched. The `else if data.length > 0` branch at X:353 is unreachable (see N1) |
| P:190-195 `skim` | X:361-363, X:547-559 | exact: tokens cached; `balanceOf(token0) − reserve0` with sub check, reading reserve0 from storage at resume; transfer; same for token1; no `_update`, no event, unlock, empty return |
| P:198-200 `sync` | X:364-365, X:560-563 | exact: two balance reads, then `_update` with reserves. The model caches reserves at entry; the source reads storage after the calls (argument order). They are equal because the pair is locked and only locked entries write reserves |
| Math.sol:6-8 `min` | AMMArithmetic.lean:15 (`min`) | exact |
| Math.sol:11-22 `sqrt` | BabylonianSqrt.lean:102-117 (`sourceResult` = Nat.sqrt for all y), model uses `Nat.sqrt` | exact |
| SafeMath.sol `add/sub/mul` | `< 2^256` and `≤` guards inline | exact (mul's `y==0 ∨ z/y==x` is the exact overflow test) |
| UQ112x112 `encode/uqdiv` | M:155-156 | exact (no uint224 wrap possible) |
| Non-payable callvalue check (every function) | X:240 | exact (none of the 27 entries is payable; empty revert) |
| Fallback / unknown selector / short calldata | not in `Entry` | not modelled at this layer; belongs to the raw decoder adapter (M:9-10, X:6-8 disclose it) |

Table summary: of the 27 entries plus the modifier and the internal helpers, every row is **exact** at the typed-source level. Exceptions: the constructor rows, where the domain separator and the factory are parameters (U8's job), and the raw-dispatch row, which is not modelled at this layer by design. I found **no semantic defect in Model.lean or Execution.lean**: rounding, SafeMath placement and order, wraparound, call order, cached-versus-storage reads, event order and return images all agree with the source. Probes that came out clean:

- Burn with `feeTo == pair`: L is cached before the fee mint in both (P:140 vs X:513).
- Re-entrant `initialize` from the factory during a swap or burn callback: tokens are cached in both (P:136-137, 167-168 vs X:336-346).
- First mint with root = 1000: `_mint(0,1000)` happens and then the liquidity guard reverts, in both.
- Supply ≠ 0 with reserve0 = 0: INVALID (division by zero) in both.
- Static context: the LOCKED, FORBIDDEN, EXPIRED and sub-underflow guards fire before the static SSTORE fault in both.
- Max allowance: no write in both.
- Skim with zero excess: a zero-amount transfer still happens in both.
- Swap with balance ≥ 2^256/1000: mul-overflow precedes the uint112 OVERFLOW in both.

## 2. Findings (ranked)

No blockers against the model. Findings S1 to S3 are statement gaps against the goal's U5 and U4 wording. They do not affect the model's correctness.

### S1. should-fix (confirmed): the run-level oracle headline does not state the U5 law; it is a bookkeeping fold that holds for any increment formula
- Lane: PropertiesOracle.lean:832-851 `runTyped_oracle_accumulates` concludes only
  `final.price0CumulativeLast = oracleFold0 st.price0CumulativeLast final.updates`, where `oracleFold0` (:106-108) adds whatever `tagged.update.increment0` was *recorded*. `Checkpoint.Accumulates` (:162-164) has no constraint linking an `OracleUpdate`'s `increment0` to its `oldReserve*`, `elapsed`, `oldTimestamp` or `timestamp` fields.
- The per-update law with `mod 2^32` exists only for a single `State.update` call (:25-55 `State.update_oracle_law`). Nothing carries it through `drive`: grep finds no use of `increment0`, `oldTimestamp` or `.elapsed` outside the fold, the step law and ModelControls:177.
- Goal U5: "each committed `_update` … adds exactly `⌊r1·2^112/r0⌋·Δt mod 2^256` … `Δt = (ts mod 2^32 − last) mod 2^32` … `blockTimestampLast := ts mod 2^32`". The control: "the statement fails if Δt is computed without mod 2^32".
- Concrete divergence: change Model.lean:153 to `let dt := ts - st.blockTimestampLast.toNat` (no wrap). `runTyped_oracle_accumulates` keeps its exact statement and stays provable, because the step law it consumes is re-derived with the changed `oracleElapsed`. So the run-level headline does not respond to the U5 control. `oracle_timestamp_mod_control` (:853-866) bites only on `State.update` itself.
- To settle: add `OracleUpdate.Lawful u` (elapsed = (u.timestamp mod 2^32 + 2^32 − u.oldTimestamp) mod 2^32 ∧ increment_i = guarded floor formula over u.oldReserve*) and a chaining predicate: first `oldTimestamp` = entry `blockTimestampLast`; each next `oldTimestamp` = previous `timestamp mod 2^32`; final `blockTimestampLast` = last `timestamp mod 2^32`; `oldReserve*` = the stored reserves before that update. Prove `∀ u ∈ final.updates, Lawful u` and the chaining through `drive`/`driveTurns` (the same induction as `drive_accumulates`). The history layer then consumes that.

### S2. should-fix (confirmed): the swap necessity theorem does not identify its balances as the post-callback answers
- Lane: PropertiesSwap.lean:28-37 `Transcript.HasDecodedWord request b t` holds if **any** `.next` node anywhere in `t` (including nested `turns`) decodes to `b`. `decodeExternal` (Execution.lean:375-399) ignores `request.site`, so `requestFor .swapBalance0 …` and `requestFor .swapBalance1 …` decode identically (both `.balanceOf pair`). `SwapTranscriptAnswers` (:78-85) is therefore symmetric in balance0 and balance1 and position-free.
- `runTyped_swap_success_conditions` (:533-553) concludes `∃ balance0 balance1, SwapModelConditions … ∧ SwapTranscriptAnswers …`. A witness pair may be, for example, (Y, Y) or (Y, X) whenever those also satisfy the K and uint112 conditions. Example: swap(out0=1, out1=0) with answers balance0 = X at swapBalance0 and balance1 = Y at swapBalance1. `HasDecodedWord req0 Y` is true via the swapBalance1 node, so the statement does not tell a consumer that the K check held over *the* post-callback answers (X, Y).
- Goal U4: "the fee-adjusted check holds over the balances *after* the transfers out and the callback".
- To settle: add `final.reserve0.val = balance0.toNat ∧ final.reserve1.val = balance1.toNat` to the conclusion (the proof already passes through `finishUpdated`), or project the answers positionally as burn does (`Transcript.firstWord`/`ownTail`, Properties.lean:1323-1330).

### S3. should-fix (confirmed): U4's later-mint, burn-payout and callback formulas exist only for the helpers, not at run level
- At run level there is only `runTyped_mint_initial` (Properties.lean:3261) for the first mint. Later mint `min(⌊a0·T/r0⌋, ⌊a1·T/r1⌋)` is `mintAmount_later_spec` (:10) on the helper. Burn `⌊L·b_i/T⌋` is `burnAmounts_spec` (:48) on the helper. "The callback runs iff data is non-empty, with exact calldata" is `Frame.afterSwapTransfer1_callback_iff` (PropertiesSwap.lean:119), a local fact about one continuation. No `runTyped_*` theorem states the returned liquidity, the credited LP amount, the burn transfer amounts or return words, or that the callback request occurs in a successful run.
- Goal U4: "Frame and model: … Later mints give … Burns pay … The flash-swap callback runs iff `data` is non-empty, with exact calldata".
- To settle: add `runTyped_mint_later` (returndata = word(min…), recipient credited, supply = T+F+L) and `runTyped_burn_payout` (returndata = [⌊L·b0/S⌋, ⌊L·b1/S⌋] with S = T+F, transfer requests carry those amounts), mirroring `runTyped_mint_initial`.

### S4. should-fix, disclosure only (confirmed): burn's NoShrink premise is not the goal's literal NoShrink, and the goal's literal premise would be wrong for burn
- Goal U3 names `NoShrink`: "the answer `balanceOf(pair)` gives in a frame is at least the stored reserve". At burn's post-transfer reads (P:150-151) an honest token answers `b_i − payout_i`, which is normally **below** the stored reserve. The literal premise therefore excludes every ordinary burn, and it would also make the burn inequality trivial (`(T−L)² ≤ T²`).
- The lane uses `BurnEntryNoShrink`/`BurnFeeNoShrink` (Properties.lean:1332-1345, 1524-1529): `r_i ≤ b_i` at the first reads, and `b_i ≤ final_i + payout_i` (the transfer debits at most the payout). This is the right ENV callee premise. It must be recorded as a stated deviation from the goal's NoShrink wording in the claim map and the completion report, not as silent drift. Sync uses the literal form (:2059-2062); mint and swap need none (:2708-2712).

### S5. note (confirmed): the U7 model control is not the goal's U7 control
- PropertiesLedger.lean:82-88 `footprintSum_dup_breaks_ledger` shows that a key duplicated *in the footprint list* breaks the sum. Goal U7's control is "a deliberately colliding key breaks conservation (`trackedSum_collision_breaks_backing` pattern)", meaning that the HASH-T storage-key premise is load-bearing. The model has no storage keys, so that control belongs to the storage/history layer. Do not count this theorem as U7's negative control.

### S6. note (confirmed, disclosed by the author): the U3(ii) rounding control is a pricing-seam witness, not a mutated model
- ModelControls.lean:3-6, 203-223 composes the unchanged `mintLP` and `update` with an upward price (2 instead of 1) on a reachable state and shows that the inequality fails. Goal U3(ii) says "not true of a mutated model where `mint` rounds up". The seam is a fair reading because every other step is the original transition, but whether it meets U3(ii) is the master's call. The U3(i) control (`noShrink_required`, :112-138) is a real kernel counterexample on a reachable sync, as required.

### N1. note: unreachable branch
Execution.lean:353-355 `else if data.length > 0 then … swapCallback` inside `startTyped` sits under `amount0Out > 0 ∨ amount1Out > 0` (X:341) after both `> 0` tests have failed, so it is dead. It is harmless to semantics, but it costs a proof case and it differs from the source shape (the source has no such branch at P:170-172). Prefer `else locked.afterSwapTransfer0 locals`, which is what PropertiesSwap.lean:1047 already normalises to.

### N2. note: gas-only divergences that U6 must respect
`mintFee` with feeTo = 0 writes `kLast := 0` unconditionally (M:184-185); the source writes only if `_kLast != 0` (P:104-105). The post-state is the same. The model's unreachable `rootK*5` and denominator overflow guards (M:194-196) are harmless.

### N3. note: adapter seams the model leaves open, correctly disclosed
- ECRECOVER output memory (`recoveryOutput`, X:84, 397).
- `v : UInt8` cleanup of the raw word (the 0.5.16 V1 decoder masks rather than rejects; the adapter must mask).
- ABI V1 short-returndata reverts (X:385, 392, 395; the prior GPT review cites disassembly at 0x214e-0x217a and 0x2770-0x279e).
- Raw selector, calldata and log encoding.

The transcript also admits `.invoke` turns under a precompile `.next`, which no real execution produces. This only over-approximates, so theorems quantified over all transcripts are stronger, not weaker.

### N4. note: frame level versus history level
`runTyped_product`, `runTyped_oracle_accumulates` and `runTyped_ledger` are top-level-frame statements. Goal U3, U5 and U7 are "History" statements; the configured-history lift was not in this review's scope.

### N5. note: comment damage from a rename
M:35 "Raw calldata and gas belong recipient the adapter", M:62 "retain source guards separately source compiler faults", X:235 "Swap infers input only source observations". These look like a mechanical `to→recipient` / `from→source` rename applied to prose. Cosmetic.

## 3. Statement check (task item 3)

| Goal item | Lane statement | Says what the goal requires? | Vacuous? |
|---|---|---|---|
| U3 fee-off | Properties.lean:2811 `runTyped_feeOff_product`: `r0·r1·T'^2 ≤ r0'·r1'·T^2` given `0 < T`, `EntryFeeOff`, `EntryNoShrink`, success; all 27 entries | yes, at frame level; premise wording per S4 | no: premises are satisfiable (ModelControls mint/donation runs); the conclusion is nontrivial (fails without NoShrink, ModelControls:112) |
| U3 fee-on | :2745 `runTyped_product` with `(T + entryFeeAmount)^2`; `feeAmount` (:574-579) = `⌊T·(√k − √kLast)/(5√k + √kLast)⌋` with separately floored roots; `mintFee_spec` (:582) ties it to the minted amount | yes | no |
| U4 first mint | :3261 `runTyped_mint_initial`, `InitialMintResult` (:2945): supply = ⌊√(a0a1)⌋, 0 credited 1000 then the recipient root−1000, return word | yes; Babylonian ≡ Nat.sqrt via BabylonianSqrt.lean:106 | no |
| U4 later mint, burn, callback | helper level only | **no** (S3) | n/a |
| U4 swap iff | PropertiesSwap.lean:533 (necessity), :1010 (sufficiency on the canonical transcript); uint112 control :1119 | partly: the necessity witnesses are not pinned to the post-callback answers (S2) | the control is real: balance 2^112 passes K and fails at OVERFLOW |
| U5 | PropertiesOracle.lean:25 (step law, exact including mod 2^32 and mod 2^256) + :832 (run-level fold) | **no** at run level (S1) | the run-level statement is nearly tautological about the formula |
| U7 | PropertiesLedger.lean:548 `runTyped_ledger` (full-address sum = supply, including address 0 and feeTo, through nested children and rollbacks), :556 footprint form | yes at frame level; the control mismatch is S5 | no: `State.empty_ledgerOn` shows the premise holds |
| Consumption | Consumption.lean:220 `runTyped_of_exact`: the exact relation implies `runTyped` equality and closure | it fixes the prior GPT review's R2 (child residue ignored): `ExactTurns.invoke` requires a closed child | no |

## 4. Verdict

**ACCEPT** for the purpose this review serves: the U2 requirement for a line-by-line correspondence table with a different-family review. The functional model (Model.lean, Execution.lean, Consumption.lean, AMMArithmetic.lean, BabylonianSqrt.lean at 2ab4868c, unchanged at lane HEAD 009d191a) matches UniswapV2Pair.sol and UniswapV2ERC20.sol v1.0.1 with no semantic defect found.

The acceptance does **not** extend to U4 or U5 completion: S1 to S3 must be closed, or explicitly scoped by the master, before U4 and U5 can be marked met. S4 must be disclosed.

Reviewer independence: Claude Opus 5.5 reviewing GPT-authored work (Codex Sol); the prior review was also GPT (Astra). The model families differ.

Commit reviewed: Blanc **2ab4868c** (uv2nh-review), plus PropertiesLedger.lean at lane HEAD **009d191a**.

Hygiene: the review snapshot `~/blanc/.worktrees/uv2nh-review` has an untracked `.uv2-source/` directory (mtime 2026-10-05 07:01:56). It predates this review, which made no writes there. The tracked files are clean.
