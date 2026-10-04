### 1. Source-to-Model-to-Bytecode Correspondence Table

| Entry / Selector | Solidity Source Line (`file:line`) | Model Definition (`file:line`) | Bytecode Refinement Theorem (`file:line`) |
| :--- | :--- | :--- | :--- |
| **`transfer`**<br>`(0xa9059cbb)` | [UniswapV2ERC20.sol:69] (`_transfer`)<br>• inlined [sub(value)]<br>• inlined [add(value)]<br>• inlined [emit Transfer] | [Model.lean:119] (`State.transferLP`)<br>• [Model.lean:124] (`Blanc.ledgerDebit`)<br>• [Model.lean:125-126] (`Blanc.ledgerCredit`)<br>• [Model.lean:127] (`.transfer`) | [TransferSource.lean:409] ([`transfer_bytecode_refines_source`])<br>[TransferSource.lean:479] ([`transfer_bytecode_exact_consumes`]) |
| | [UniswapV2ERC20.sol:70] (`return true;`) | [Execution.lean:250] (`startImmediate`, `encodeWords [1]`) | [TransferSource.lean:409] ([`transfer_bytecode_refines_source`]) |
| **`approve`**<br>`(0x095ea7b3)` | [UniswapV2ERC20.sol:64] (`_approve`)<br>• inlined [allowance = value]<br>• inlined [emit Approval] | [Model.lean:131] (`State.approveLP`)<br>• [Model.lean:134] (`Function.update st.allowance`)<br>• [Model.lean:134] (`.approval`) | [ApproveSource.lean:213] ([`approve_bytecode_refines_source`])<br>[ApproveSource.lean:259] ([`approve_bytecode_exact_consumes`]) |
| | [UniswapV2ERC20.sol:65] (`return true;`) | [Execution.lean:248] (`startImmediate`, `encodeWords [1]`) | [ApproveSource.lean:213] ([`approve_bytecode_refines_source`]) |
| **`transferFrom`**<br>`(0x23b872dd)`<br>*(max allowance)* | [UniswapV2ERC20.sol:74] (`if != uint(-1)`, false: bypass subtraction) | [Model.lean:139] (`st.allowance source ctx.sender = B256.max`) | [TransferFromSource.lean:527] ([`transferFrom_bytecode_refines_source`])<br>[TransferFromEntries.lean:97] ([`transferFrom48_selected_inv`], `.inl`) |
| **`transferFrom`**<br>`(0x23b872dd)`<br>*(finite allowance)* | [UniswapV2ERC20.sol:74-76] (`allowance = allowance.sub(value)`) | [Model.lean:140-144] (`reduced := { ... allowance := update ... }`) | [TransferFromSource.lean:527] ([`transferFrom_bytecode_refines_source`])<br>[TransferFromEntries.lean:97] ([`transferFrom48_selected_inv`], `.inr`) |
| **`transferFrom`**<br>`(0x23b872dd)`<br>*(shared tail)* | [UniswapV2ERC20.sol:77] (`_transfer(from, to, value);`) | [Model.lean:119-129] (`State.transferLP` dispatched at 139, 144) | [TransferFromSource.lean:527] ([`transferFrom_bytecode_refines_source`])<br>[TransferFromSource.lean:603] ([`transferFrom_bytecode_exact_consumes`]) |
| | [UniswapV2ERC20.sol:78] (`return true;`) | [Execution.lean:252] (`startImmediate`, `encodeWords [1]`) | [TransferFromSource.lean:527] ([`transferFrom_bytecode_refines_source`]) |
| **`initialize`**<br>`(0x485cc955)` | [UniswapV2Pair.sol:67] (`require(msg.sender == factory, ...)`) | [Execution.lean:254] (`if ctx.sender = st.factory then ...`) | [InitializeSource.lean:199] ([`initialize_bytecode_refines_source`])<br>[InitializeCore.lean:208] ([`initialize45_inv`]) |
| | [UniswapV2Pair.sol:68] (`token0 = _token0;`) | [Execution.lean:257] (`post := { st with token0 := token0 ... }`) | [InitializeSource.lean:199] ([`initialize_bytecode_refines_source`])<br>[InitializeCore.lean:23] ([`initializeWrites_exact`]) |
| | [UniswapV2Pair.sol:69] (`token1 = _token1;`) | [Execution.lean:257] (`post := { ... token1 := token1 }`) | [InitializeSource.lean:199] ([`initialize_bytecode_refines_source`])<br>[InitializeCore.lean:23] ([`initializeWrites_exact`]) |
| **`name`** | [UniswapV2ERC20.sol:9] (`string public constant name = ...`) | [Execution.lean:27] (`getterResult .name`) | [GetterStringWalk.lean:903] ([`getterString_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`symbol`** | [UniswapV2ERC20.sol:10] (`string public constant symbol = ...`) | [Execution.lean:28] (`getterResult .symbol`) | [GetterStringWalk.lean:903] ([`getterString_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`decimals`** | [UniswapV2ERC20.sol:11] (`uint8 public constant decimals = 18;`) | [Execution.lean:29] (`getterResult .decimals`) | [GetterScalarWalk.lean:76] ([`decimals_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`MINIMUM_LIQUIDITY`** | [UniswapV2Pair.sol:15] (`uint public constant MINIMUM_LIQUIDITY = 10**3;`) | [Execution.lean:30] (`getterResult .minimumLiquidity`) | [GetterScalarWalk.lean:97] ([`minimumLiquidity_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`PERMIT_TYPEHASH`** | [UniswapV2ERC20.sol:18] (`bytes32 public constant PERMIT_TYPEHASH = ...`) | [Execution.lean:31] (`getterResult .permitTypehash`) | [GetterScalarWalk.lean:118] ([`permitTypehash_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`totalSupply`** | [UniswapV2ERC20.sol:12] (`uint public totalSupply;`) | [Execution.lean:32] (`getterResult .totalSupply`) | [GetterWalk.lean:478] ([`totalSupply_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`balanceOf`** | [UniswapV2ERC20.sol:13] (`mapping(address => uint) public balanceOf;`) | [Execution.lean:33] (`getterResult (.balanceOf owner)`) | [GetterStorageMappingWalk.lean:100] ([`balanceOf_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`allowance`** | [UniswapV2ERC20.sol:14] (`mapping(address => mapping(...)) public allowance;`) | [Execution.lean:34] (`getterResult (.allowance owner spender)`) | [GetterStorageMappingWalk.lean:191] ([`allowance_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`DOMAIN_SEPARATOR`** | [UniswapV2ERC20.sol:16] (`bytes32 public DOMAIN_SEPARATOR;`) | [Execution.lean:35] (`getterResult .domainSeparator`) | [GetterScalarWalk.lean:139] ([`domainSeparator_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`nonces`** | [UniswapV2ERC20.sol:19] (`mapping(address => uint) public nonces;`) | [Execution.lean:36] (`getterResult (.nonces owner)`) | [GetterStorageMappingWalk.lean:129] ([`nonces_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`factory`** | [UniswapV2Pair.sol:18] (`address public factory;`) | [Execution.lean:37] (`getterResult .factory`) | [GetterScalarWalk.lean:231] ([`factory_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`token0`** | [UniswapV2Pair.sol:19] (`address public token0;`) | [Execution.lean:38] (`getterResult .token0`) | [GetterScalarWalk.lean:254] ([`token0_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`token1`** | [UniswapV2Pair.sol:20] (`address public token1;`) | [Execution.lean:39] (`getterResult .token1`) | [GetterScalarWalk.lean:277] ([`token1_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`getReserves`** | [UniswapV2Pair.sol:39-41] (`_reserve0 = ...; _reserve1 = ...; _blockTimestampLast = ...;`) | [Execution.lean:40-41] (`getterResult .getReserves`) | [GetterStorageReservesWalk.lean:41] ([`getReserves_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`price0CumulativeLast`** | [UniswapV2Pair.sol:26] (`uint public price0CumulativeLast;`) | [Execution.lean:42] (`getterResult .price0CumulativeLast`) | [GetterScalarWalk.lean:162] ([`price0CumulativeLast_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`price1CumulativeLast`** | [UniswapV2Pair.sol:27] (`uint public price1CumulativeLast;`) | [Execution.lean:43] (`getterResult .price1CumulativeLast`) | [GetterScalarWalk.lean:185] ([`price1CumulativeLast_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |
| **`kLast`** | [UniswapV2Pair.sol:28] (`uint public kLast;`) | [Execution.lean:44] (`getterResult .kLast`) | [GetterScalarWalk.lean:208] ([`kLast_bytecode_refines`])<br>[StaticViewSource.lean:139] ([`staticView_source_handler_selected`]) |

---

### 2. Failure-Branch Coverage Table

| Entry / Selector | Deployed Bytecode Revert Condition | Existing Lean Exclusion Declaration (shows `.ok` run avoids revert) | Status |
| :--- | :--- | :--- | :--- |
| **`transfer`**<br>`(0xa9059cbb)` | Nonzero `callvalue` (`t_0000_c0` revert) | [TransferSource.lean:417] ([`transfer_bytecode_refines_source`], `sevm.value = 0`), [TransferEntries.lean:319] ([`transfer_pc0_inv`]) | Covered |
| | Short calldata selector (`length < 4`) | [TransferEntries.lean:319] ([`transfer_pc0_inv`], `4 ≤ sevm.data.length.toB256`), [GetterWalk.lean:301] ([`getter_guards_inv`]) | Covered |
| | Short calldata args (`length < 68`, `t_0570_c85`) | [TransferSource.lean:417] ([`transfer_bytecode_refines_source`], `68 ≤ sevm.data.length`), [TransferEntries.lean:163] ([`transfer_entry_inv`]) | Covered |
| | Static context write (`isStatic = true`) | [TransferSource.lean:417] ([`transfer_bytecode_refines_source`], `sevm.isStatic = false`), [TransferEntries.lean:122] ([`transfer_decoder_inv`]), [TransferCore.lean:745] ([`transfer40_inv`]) | Covered |
| | SafeMath `sub` underflow on sender balance | [TransferSource.lean:420] ([`transfer_bytecode_refines_source`], `cover`), [TransferCore.lean:681] ([`sub59_inv`]) | Covered |
| | SafeMath `add` overflow on recipient balance | [TransferSource.lean:420] ([`transfer_bytecode_refines_source`], `nowrap`), [TransferEntries.lean:33] ([`transferCreditSafe`]) | Covered |
| **`approve`**<br>`(0x095ea7b3)` | Nonzero `callvalue` (`t_0000_c0` revert) | [ApproveSource.lean:221] ([`approve_bytecode_refines_source`], `sevm.value = 0`), [GetterWalk.lean:301] ([`getter_guards_inv`]) | Covered |
| | Short calldata selector (`length < 4`) | [ApproveSource.lean:78] ([`approve_word_guards_iff`]), [GetterWalk.lean:301] ([`getter_guards_inv`]) | Covered |
| | Short calldata args (`length < 68`, `t_0360_c86`) | [ApproveSource.lean:221] ([`approve_bytecode_refines_source`], `68 ≤ sevm.data.length`), [ApproveSource.lean:78] ([`approve_word_guards_iff`]) | Covered |
| | Static context write (`isStatic = true`) | [ApproveSource.lean:221] ([`approve_bytecode_refines_source`], `sevm.isStatic = false`), [ApproveSource.lean:145] ([`approve_startImmediate_inv`]) | Covered |
| | SafeMath arithmetic | *[Inference]* N/A: `approve` performs direct storage assignment without arithmetic. | N/A |
| **`transferFrom`**<br>`(0x23b872dd)` | Nonzero `callvalue` (`t_0000_c0` revert) | [TransferFromSource.lean:535] ([`transferFrom_bytecode_refines_source`], `sevm.value = 0`), [TransferFromEntries.lean:537] ([`transferFrom_pc0_inv`]) | Covered |
| | Short calldata selector (`length < 4`) | [TransferFromEntries.lean:537] ([`transferFrom_pc0_inv`], `4 ≤ sevm.data.length.toB256`), [GetterWalk.lean:301] ([`getter_guards_inv`]) | Covered |
| | Short calldata args (`length < 100`, `t_0e36_c48`) | [TransferFromSource.lean:535] ([`transferFrom_bytecode_refines_source`], `100 ≤ sevm.data.length`), [TransferFromEntries.lean:538] ([`transferFrom_pc0_inv`]) | Covered |
| | Allowance underflow (`allowance != -1` and `allowance < value`) | [TransferFromSource.lean:537] ([`transferFrom_bytecode_refines_source`], `allowed`), [TransferFromEntries.lean:97] ([`transferFrom48_selected_inv`], `.inr`), [TransferFromEntries.lean:57] ([`transferFromAllowanceSafe`]) | Covered |
| | Max allowance bypass (`allowance == -1`) | [TransferFromEntries.lean:97] ([`transferFrom48_selected_inv`], `.inl same`), [TransferFromSource.lean:231] ([`transferFromLP_accept`]) | Covered |
| | Static context write (`isStatic = true`) | [TransferFromSource.lean:535] ([`transferFrom_bytecode_refines_source`], `sevm.isStatic = false`), [TransferFromEntries.lean:540] ([`transferFrom_pc0_inv`]) | Covered |
| | SafeMath `sub` underflow on sender balance | [TransferFromSource.lean:537] ([`transferFrom_bytecode_refines_source`], `cover`), [TransferFromEntries.lean:539] ([`transferFrom_pc0_inv`]) | Covered |
| | SafeMath `add` overflow on recipient balance | [TransferFromSource.lean:537] ([`transferFrom_bytecode_refines_source`], `nowrap`), [TransferFromEntries.lean:540] ([`transferFrom_pc0_inv`], `transferFromCreditSafe`) | Covered |
| **`initialize`**<br>`(0x485cc955)` | Nonzero `callvalue` (`t_0000_c0` revert) | [InitializeSource.lean:206] ([`initialize_bytecode_refines_source`], `sevm.value = 0`), [InitializeEntries.lean:201] ([`initialize_dispatch_exact`]) | Covered |
| | Short calldata selector (`length < 4`) | [GetterWalk.lean:301] ([`getter_guards_inv`]), [InitializeEntries.lean:201] ([`initialize_dispatch_exact`]) | Covered |
| | Short calldata args (`length < 68`, `t_0430_c90`) | [InitializeSource.lean:206] ([`initialize_bytecode_refines_source`], `68 ≤ sevm.data.length`), [InitializeEntries.lean:160] ([`initialize_entry_inv`]) | Covered |
| | Unauthorized caller (`caller != factory`, `t_0f4c_c45`) | [InitializeSource.lean:206] ([`initialize_bytecode_refines_source`], `caller = factory`), [InitializeCore.lean:208] ([`initialize45_inv`]), [InitializeEntries.lean:88] ([`initialize_decoder_inv`]) | Covered |
| | Static context write (`isStatic = true`) | [InitializeSource.lean:207] ([`initialize_bytecode_refines_source`], `sevm.isStatic = false`), [InitializeCore.lean:84] ([`initializeWrites_inv`]), [InitializeCore.lean:208] ([`initialize45_inv`]) | Covered |
| **All 17 Getters** | Nonzero `callvalue` (`t_0000_c0` revert) | [StaticViewSource.lean:149] ([`staticView_source_handler_selected`], `sevm.value = 0`), [StaticViewSource.lean:188] ([`staticView_source_handler_inv`]), [GetterWalk.lean:301] ([`getter_guards_inv`]) | Covered |
| | Short calldata selector (`length < 4`) | [GetterWalk.lean:301] ([`getter_guards_inv`]), [StaticViewSource.lean:150] ([`staticView_source_handler_selected`]) | Covered |
| **`balanceOf`, `nonces`** | Short calldata 1-arg (`length < 36`, `reject`) | [GetterStorageMappingWalk.lean:70] ([`singleMapping_bytecode_refines`], `32 ≤ data.length - 4`), [GetterStorageMappingDecoder.lean:148] ([`singleMapping_entry_inv`]), [StaticViewSource.lean:150] (`argumentSize + 4 ≤ length`) | Covered |
| **`allowance`** | Short calldata 2-arg (`length < 68`, `t_0652_c77`) | [GetterStorageMappingWalk.lean:198] ([`allowance_bytecode_refines`], `64 ≤ data.length - 4`), [GetterStorageMappingDecoder.lean:292] ([`allowance_entry_inv`]) | Covered |
| **14 0-arg Getters** | Short argument calldata | *[Fact]* `argumentSize = 0` ([StaticViewSource.lean:45]); no argument length guard exists in bytecode. | N/A |
| **All 17 Getters** | Static context write | *[Fact]* No getter contains SSTORE instructions; static calls are explicitly admitted without failure ([StaticViewSource.lean:186]). | N/A |
| **All 17 Getters** | SafeMath underflow / overflow | *[Inference]* N/A: pure storage-read / constant-return routines with no arithmetic. | N/A |

---

### 3. GAP List

**No gaps found.**

Every bytecode failure branch for all specified entrypoints (`transfer`, `approve`, `transferFrom` in both branches, `initialize`, and the 17 static getters) is accounted for by existing Lean guard-inversion lemmas, entry-inversion theorems, or refinement conclusions. Specifically:
- **Payable guards (`callvalue = 0`)**: Excluded across all entries by [GetterWalk.lean:301] (`getter_guards_inv`) and individual refinement theorems.
- **Calldata length bounds**: Minimum selector length (`4 ≤ length`) and decoded argument sizes (`68` for `transfer`/`approve`/`initialize`, `100` for `transferFrom`, `36` for single mappings, `68` for double mappings) are proved by respective `*_entry_inv` and `*_bytecode_refines_source` theorems.
- **Static context restrictions**: State-mutating entries (`transfer`, `approve`, `transferFrom`, `initialize`) all conclude `isStatic = false` via sstore-reversion exclusion ([`of_run_sstore_not_static`]).
- **Access control**: The `UniswapV2: FORBIDDEN` guard in `initialize` is excluded by [InitializeCore.lean:208] (`initialize45_inv`), which disproves `t_0f4c_c45` via [`false_of_noOk`] and establishes `sevm.caller = current.state.factory`.
- **SafeMath arithmetic**: Sender balance underflow and recipient balance overflow in `transfer` and `transferFrom`, as well as finite allowance underflow in `transferFrom`, are eliminated via [`sub59_inv`] and [`transferCreditSafe`] / [`transferFromAllowanceSafe`].
