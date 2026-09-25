<!-- GENERATED FILE — do not edit by hand. -->
<!-- Regenerate with: python3 scripts/generate-proof-recipes.py --write -->

# Blanc proof recipes

Generated from scripts/proof-recipes.toml; do not edit by hand.

Consult these recipes before beginning a manual multi-step walk or inversion.
A suggestion is guidance, not a proof that its recipe applies at a particular goal.

## `tagged-storage-region-separation`

- Status: `active`
- Triggers: `goal-shape:tagged-storage-region-separation`
- Preferred path: For two `TaggedStorage.encode` keys with regions below 16, payloads below `2^252`, and unequal regions, apply `TaggedStorage.encode_ne_of_region_ne`. For a fixed region, use `TaggedStorage.encode_injective_of_payload_lt`; use `TaggedStorage.encode_eq_of_payload_lt` to bridge an existing unmasked `OR` encoder only after proving its payload bound.
- Boundary: The encoder masks payload bits at and above bit 252, so unbounded payload injectivity is false; natural regions also wrap modulo the 256-bit word width, so unbounded region separation is false. This is logical key construction, not Solidity address-slot read or assignment semantics, and it proves no family hash/payload injectivity.
- Owner module: [Blanc/TaggedStorage.lean](../Blanc/TaggedStorage.lean)
- Canonical example: [Blanc/TaggedStorage.lean](../Blanc/TaggedStorage.lean) — `encode_ne_of_region_ne`
- Registered symbols: `module:Blanc/TaggedStorage.lean`, `declaration:Blanc.TaggedStorage.encode`, `declaration:Blanc.TaggedStorage.encode_eq_of_payload_lt`, `declaration:Blanc.TaggedStorage.encode_injective_of_payload_lt`, `declaration:Blanc.TaggedStorage.encode_ne_of_region_ne`
- Review: `proof-infrastructure` on `2026-09-09`

## `same-frame-stack-certificate`

- Status: `active`
- Triggers: `goal-head:CompiledStackSafety.StepSafe`, `goal-head:CompiledStackSafety.ResumeSafe`
- Preferred path: Use CompiledStackSafety.Certificate.at_parentPrefix for a checked certificate and an actual same-frame prefix, deriving the exact root entry invariant first. Use resume_call_safe to close an actual CALL resumption from parent headroom and its continuation stack invariant; call_resumes_of_room constructs the actual status-word result.
- Boundary: The certificate requires local proofs for actual decoded steps; a symbolic PC/height table alone is insufficient. The theorem covers arbitrary raw parent outcomes but does not assert safety of arbitrary entered child code. Fatal child errors are distinguished from newly generated parent stack faults.
- Owner module: [Blanc/CompiledStackSafety.lean](../Blanc/CompiledStackSafety.lean)
- Canonical example: [Blanc/CompiledStackSafety.lean](../Blanc/CompiledStackSafety.lean) — `Certificate.at_parentPrefix`
- Registered symbols: `declaration:Blanc.CompiledStackSafety.Certificate`, `declaration:Blanc.CompiledStackSafety.Certificate.parentStep`, `declaration:Blanc.CompiledStackSafety.Certificate.parentPrefix`, `declaration:Blanc.CompiledStackSafety.Certificate.at_parentPrefix`, `declaration:Blanc.CompiledStackSafety.call_resumes_of_room`, `declaration:Blanc.CompiledStackSafety.resume_call_safe`
- Review: `proof-infrastructure` on `2026-09-06`

## `runcompiled-construction`

- Status: `active`
- Triggers: `goal-head:Func.RunCompiled`, `goal-head:Func.RunCompiledTo`, `goal-head:Func.ExecTo`, `goal-head:Func.ExecWitness`
- Preferred path: Use `func_run` and its registered opcode arms. For `MSTORE` and `MSTORE8`, pass the dynamic memory-expansion charge as the next numeric hint; the `MSTORE8` arm preserves the exact singleton low-byte write and leaves `devm.extCost [⟨i.toNat, 1⟩] = e` as an explicit obligation. Before walking a large concrete body, apply the term-size breaker: the pathological case is a walk whose intermediate term carries the whole concrete remaining program, memory or value, and its signature is a `maxRecDepth`/`maxHeartbeats` ceiling over a multi-`MSTORE` staging run. Factor such a walk into named sub-components, abstract each over the memory or value it threads — a carrier structure over a variable, as `ConstructorPatchInvariant` does in `Blanc/LidoCircuitBreakerDeploymentTrace.lean` — and instantiate the concrete facts through named top-level lemmas, so one layer over a variable stays small instead of composing multiplicatively. Build each certificate separately and abstract only those that cross the breaker; the abstraction is not free and a short bounded walk does not need it. For residual-cost attribution, opt in with the default-off `Blanc.Forward.discharge` trace and aggregate it with `scripts/read-discharge-trace.py` before changing a fallback.
- Boundary: This constructs a compiled walk; numeric memory hints are checked against the semantic `extCost` premise, so dynamic expansion remains explicit. It does not invert an existing run, replace a completed continuation with a summary, synthesize a parallel path certificate, or optimize route data before proof construction. Expensive source and value classes are heterogeneous, so there is no shared discharge fold. Consider local sub-component or carrier abstraction only for oversized concrete intermediates, and judge the owning closure rather than an isolated target. In the tested `runcompiled-construction` contexts, the `UnregisterRegistration` body-from-kernel summary required a new recursion ceiling and was reverted, while cross-module placement in `RegistrySubstrate` made the gate red. Those results close those attempts in those contexts, not the local sub-component route above or the distinct successful private summaries documented by `runcompiled-family-compression`. Reuse a cold-entry helper only when the same accumulated prefix recurs in a measured owner. Current local examples: `ConstructorPatchInvariant` in `Blanc/LidoCircuitBreakerDeploymentTrace.lean`; `PauseStageMemory` and its pause-walk route in `Blanc/LidoCircuitBreakerPauseWalk.lean`; replacement guard-prefix certificates leading to `replacementRegisterPauserBody_fromStage_runCompiled` in `Blanc/LidoCircuitBreakerReplacementRegistration.lean`; `freshRegisterPauserBody_fromStage_runCompiled`; and `absentZeroRegisterPauserBody_fromStage_runCompiled`. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `runcompiled-construction`.
- Owner module: [Blanc/Forward.lean](../Blanc/Forward.lean)
- Canonical example: [Blanc/Weth10Redeemable.lean](../Blanc/Weth10Redeemable.lean) — `withdrawTo_progExecSat`
- Registered symbols: `tactic:func_run`, `declaration:Func.RunCompiled`, `declaration:Func.RunCompiledTo`, `declaration:Func.ExecTo`, `declaration:Func.ExecWitness`, `declaration:Ninst.runCompiled_mstore8_of`
- Review: `proof-infrastructure` on `2026-09-09`

## `linear-dispatch-selection`

- Status: `active`
- Triggers: `goal-shape:linear-dispatch-selection`
- Preferred path: For an existing `Func.RunCompiledTo` walk rooted at `Blanc.linearDispatchWith`, use `dispatchBodyWitness_of_runCompiledTo` for a selector hit or `dispatchFallbackWitness_of_runCompiledTo` for a miss. A hit supplies selector uniqueness and selected-entry membership; a miss supplies a nonempty entry list and exclusion from every entry. Both start from `selector :: tail`, remove the selector, recover the exact body or fallback call, and preserve the dispatch frame outside stack and gas. To construct an arbitrary-outcome all-miss route forward from a fallback-body witness, use `Func.execWitness_linearDispatchWith_fallback` with the exact `linearDispatchFallbackCost` budget. Compose frame facts with `Devm.DispatchFramePreserved.trans` and the push/pop/diff-burn adapters.
- Boundary: The neutral theorems discharge only dispatcher opcode inversions or constructive all-miss opcode execution. They do not know a contract's selector census, calldata ABI, role storage, auxiliary rebasing, or selected-body/fallback semantics.
- Owner module: [Blanc/LinearDispatchCorrectness.lean](../Blanc/LinearDispatchCorrectness.lean)
- Canonical example: [Blanc/LinearDispatchCorrectness.lean](../Blanc/LinearDispatchCorrectness.lean) — `dispatchBodyWitness_of_runCompiledTo`
- Registered symbols: `module:Blanc/LinearDispatch.lean`, `module:Blanc/LinearDispatchCorrectness.lean`, `declaration:Blanc.linearDispatchWith`, `declaration:Blanc.selectorUnique`, `declaration:Blanc.Devm.DispatchFramePreserved`, `declaration:Blanc.Devm.DispatchFramePreserved.trans`, `declaration:Blanc.dispatchFrame_of_pushBurn`, `declaration:Blanc.dispatchFrame_of_popBurnBy`, `declaration:Blanc.dispatchFrame_of_diffBurn`, `declaration:Blanc.DispatchBodyWitness`, `declaration:Blanc.dispatchBodyWitness_of_runCompiledTo`, `declaration:Blanc.DispatchFallbackWitness`, `declaration:Blanc.dispatchFallbackWitness_of_runCompiledTo`, `declaration:Blanc.linearDispatchFallbackCost`, `declaration:Blanc.Func.execWitness_linearDispatchWith_fallback`
- Review: `proof-infrastructure` on `2026-08-29`

## `line-run-split`

- Status: `active`
- Triggers: `implication-premise:Line.Run`
- Preferred path: Use `line_execute` or `line_execute_with`; revert a named run premise first when needed.
- Boundary: The tactic performs one split and does not automatically transport an arbitrary set of observations.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/Conserved.lean](../Blanc/Conserved.lean) — `Fmint.of_prepApprove`
- Registered symbols: `tactic:line_execute`, `tactic:line_execute_with`, `declaration:Line.Run`
- Review: `proof-infrastructure` on `2026-08-20`

## `func-run-prefix-split`

- Status: `active`
- Triggers: `implication-premise:Func.Run`
- Preferred path: Use `func_execute n` or `func_execute_with line` to expose a known prefix. For a successful conditional whose selected arm calls a known nonreturning auxiliary, use `of_run_branch_call_of_not_run`; the `revert`, `revertWith`, and `revertReturnData` specializations discharge the standard reverter bodies.
- Boundary: This targets the older implication-shaped `Func.Run`; it is not `RunCompiled` construction and does not invert an arbitrary named derivation without first reverting it. The nonreturning-call inversion proves only that the successful walk selected the zero/fall-through arm; transport any stack or state observation separately from its returned `Devm.PopBurn`.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Solvent.lean](../Blanc/Solvent.lean) — `withdraw_preserves_solvent`
- Registered symbols: `tactic:func_execute`, `tactic:func_execute_with`, `declaration:Func.Run`, `declaration:Blanc.of_run_branch_call_of_not_run`, `declaration:Blanc.of_run_branch_call_revert`, `declaration:Blanc.of_run_branch_call_revertWith`, `declaration:Blanc.of_run_branch_call_revertReturnData`, `declaration:Blanc.Func.not_run_revertReturnData`
- Review: `proof-infrastructure` on `2026-08-20`

## `static-store-exclusion`

- Status: `active`
- Triggers: `implication-premise:Func.Run`
- Preferred path: Prove `StoresOrHalts fs f`, then apply `StoresOrHalts.isStatic_eq_false` to the exact successful source run `Func.Run fs e s f r` to derive `e.isStatic = false`. Use `stores_structure` for instruction and branch structure. Before a long staging line, use `stores_line line` with the exact `Line` prefix supplied explicitly; the driver does not search for an arbitrary split. Handle contract-specific calls explicitly with `StoresOrHalts.call` or the `with` arm.
- Boundary: Every successful path must reach `SSTORE` or be impossible under the universal non-run premise of `StoresOrHalts.never`; a body with an executable `Func.stop` arm is outside the relation. The theorem does not construct a run, identify the written key or value, or prove a storage effect.
- Owner module: [Blanc/StaticStores.lean](../Blanc/StaticStores.lean)
- Canonical example: [Blanc/LidoTriggerableWithdrawalsGatewayStaticStores.lean](../Blanc/LidoTriggerableWithdrawalsGatewayStaticStores.lean) — `setLimitWrite_storesOrHalts`
- Registered symbols: `module:Blanc/StaticStores.lean`, `declaration:Blanc.StoresOrHalts`, `declaration:Blanc.StoresOrHalts.prepend`, `declaration:Blanc.StoresOrHalts.isStatic_eq_false`, `tactic:stores_structure`, `tactic:stores_line`
- Review: `proof-infrastructure` on `2026-09-08`

## `stack-prefix-transport`

- Status: `active`
- Triggers: `goal-shape:stack-prefix-line-run`
- Preferred path: Use `line_prefix` or `generalize_line_prefix`, with `show_pref` for concrete prefix goals. For a known MUL, DIV, ADDMOD, MULMOD, TIMESTAMP, XOR, or non-address argument-check step, use the corresponding `prefix_of_*` declaration directly when the tactic has no registered arm.
- Boundary: `line_prefix` supports a finite instruction set and refuses instructions without a registered case. The direct `prefix_of_*` lemmas transport only the named stack prefix; combine them with a separate observation invariant when more state must be carried.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Weth10HolderFlowCompiled.lean](../Blanc/Weth10HolderFlowCompiled.lean) — `recognized_of_run_dispatchWith`
- Registered symbols: `tactic:line_prefix`, `tactic:generalize_line_prefix`, `tactic:show_pref`, `declaration:prefix_of_mul`, `declaration:prefix_of_div`, `declaration:prefix_of_addmod`, `declaration:prefix_of_mulmod`, `declaration:prefix_of_timestamp`, `declaration:prefix_of_xor`, `declaration:prefix_of_argCheckNonAddress`
- Review: `proof-infrastructure` on `2026-08-20`

## `state-context-cleanup`

- Status: `active`
- Triggers: `context-shape:intermediate-devm`
- Preferred path: Use `clear_state hState` after transporting every fact that must survive.
- Boundary: This destructive cleanup removes the state and every local fact that depends on it. Check whether a usable completed continuation summary already discharges the goal, and transport every fact that must survive. The context-count heuristic is only a prompt, never an automatic cleanup command; it cannot determine whether such a summary exists. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `state-context-cleanup`.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Conserved.lean](../Blanc/Conserved.lean) — `Fmint.of_prepApprove`
- Registered symbols: `tactic:clear_state`
- Review: `proof-infrastructure` on `2026-08-21`

## `line-observation-invariance`

- Status: `active`
- Triggers: `goal-head:Line.Inv`, `goal-head:Ninst.Inv`, `goal-head:Rinst.Inv`
- Preferred path: Use `line_inv` through the registered `Ninst.Hinv` and `Rinst.Hinv` instances.
- Boundary: A missing contract-neutral instance belongs in the lowest common upstream layer; contract-specific semantic facts do not.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Weth10HolderFlowCompiled.lean](../Blanc/Weth10HolderFlowCompiled.lean) — `Devm.DispatchSilent.of_pushEq`
- Registered symbols: `tactic:line_inv`, `declaration:Line.Inv`, `declaration:Ninst.Inv`, `declaration:Rinst.Inv`, `declaration:Ninst.Hinv`, `declaration:Rinst.Hinv`
- Review: `proof-infrastructure` on `2026-08-20`

## `function-observation-invariance`

- Status: `active`
- Triggers: `goal-head:Func.Inv`, `goal-head:Linst.Inv`
- Preferred path: For `Func.Inv`, use `func_inv` to assemble the function invariant from registered line and terminal invariants. For a terminal `Linst.Inv`, use the registered instance directly with `exact Linst.Hinv.inv`.
- Boundary: `func_inv` deliberately refuses `Func.call`, whose callee is arbitrary under `Func.Inv`; fix the context or factor through the entry. A missing terminal instance belongs in the lowest common shared module, not in a contract consumer.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Solvent.lean](../Blanc/Solvent.lean) — `approve_preserves_bal`
- Registered symbols: `tactic:func_inv`, `declaration:Func.Inv`, `declaration:Linst.Inv`, `declaration:Linst.Hinv`
- Review: `proof-infrastructure` on `2026-08-20`

## `call-boundary-outcomes`

- Status: `active`
- Triggers: `goal-head:Func.ExecSat`, `goal-head:Prog.ExecSat`, `goal-head:Func.ExecWitness`
- Preferred path: Use the `ForwardCall` module and the live `ExecSat`/`ExecWitness` layer to cross calls or package multiple outcomes. At a proof-carrying `DELEGATECALL` boundary, use `DelegatecallSpawnDescriptor.step` for the exact spawn and `.crossing` for the entered child's successful continuation instead of reconstructing the descriptor fields at the consumer. To construct the compiled call from a retained child and exact resume equation, use `DelegatecallSpawnDescriptor.runCompiled_of_certificate`. When an existing compiled call step has already resumed, use `DelegatecallSpawnDescriptor.settled_of_runCompiled` to obtain a `DelegatecallSettledBoundary` with the exact retained child and parent observations. Use `DelegatecallSettledBoundary.memory_image_of_outputSize_zero` to carry a proof-carrying memory image across a zero-output child resume. To invert an existing source `Ninst.Run` over a direct call with known operands, use the `Blanc/LadderBase.lean` inversion pair: `of_run_call_val_with_depth_frame` for the 7-operand CALL prefix (failed arm: flag `0` + `Devm.WorldEq`; entered arm: `Ninst.StepRun`, depth, exact parent/message/resume equations; compat projections `of_run_call_val_with_depth`, `of_run_call_val`) and `of_run_staticcall_val_with_depth_cause` for the 6-operand STATICCALL prefix (failed arm carries `StatcallFailureCause`; compat projection `of_run_staticcall_val_with_depth`). Dismiss the failed arm with the trailing `iszero`+guard, align the entered step with `Ninst.StepRun.unique_exec_of_filled`, and take `RawCommits` from `ProcessMessage.settlementCommits_of_some_ok_clean`. For child code/address from a spawn equation without operand knowledge, use the `Blanc/CommonProofs.lean` spawn-source family: the `Xinst.step_spawn_source` trichotomy (whose same-target disjunct is explicitly open), `Xinst.step_spawn_codeAddress_eq_currentTarget`, and `Evm.step_spawn_child` for the away-from-parent cases.
- Boundary: Do not duplicate the settlement/determinism tail, and do not infer deadness from qualified-name grep alone. CALL (7 operands, value, stipend) and STATICCALL (6 operands, forced static) have separate inversion statements: select by operand count, never by analogy. The inversion pair inverts an existing run and never manufactures liveness from a prefix; the spawn-source trichotomy's same-target disjunct is open and must be reported, not forced.
- Owner module: [Blanc/ForwardCall.lean](../Blanc/ForwardCall.lean)
- Canonical example: [Blanc/Weth10Redeemable.lean](../Blanc/Weth10Redeemable.lean) — `withdrawTo_progExecSat`
- Registered symbols: `module:Blanc/ForwardCall.lean`, `module:Blanc/DelegatecallEnvelope.lean`, `declaration:Func.ExecSat`, `declaration:Prog.ExecSat`, `declaration:Func.ExecWitness`, `declaration:Prog.ExecWitness`, `declaration:DelegatecallSpawnDescriptor.afterAccess_memory`, `declaration:DelegatecallSpawnDescriptor.step`, `declaration:DelegatecallSpawnDescriptor.child_data`, `declaration:DelegatecallSpawnDescriptor.crossing`, `declaration:DelegatecallSpawnDescriptor.runCompiled_of_certificate`, `declaration:DelegatecallSettledBoundary`, `declaration:DelegatecallSpawnDescriptor.settled_of_runCompiled`, `declaration:DelegatecallSettledBoundary.memory`, `declaration:DelegatecallSettledBoundary.memory_eq_parent_of_outputSize_zero`, `declaration:DelegatecallSettledBoundary.memory_image_of_outputSize_zero`, `module:Blanc/LadderBase.lean`, `module:Blanc/CommonProofs.lean`, `declaration:Blanc.of_run_call_val_with_depth_frame`, `declaration:Blanc.of_run_call_val_with_depth`, `declaration:Blanc.of_run_call_val`, `declaration:Blanc.StatcallFailureCause`, `declaration:Blanc.of_run_staticcall_val_with_depth_cause`, `declaration:Blanc.of_run_staticcall_val_with_depth`, `declaration:Blanc.Xinst.step_spawn_source`, `declaration:Blanc.Xinst.step_spawn_codeAddress_eq_currentTarget`, `declaration:Blanc.Evm.step_spawn_child`
- Review: `proof-infrastructure` on `2026-08-30`

## `devm-projection-bridge`

- Status: `active`
- Triggers: `goal-shape:devm-update-projection`
- Preferred path: Rewrite with the matching Jaune update-first projection lemma, named `Devm.<update>_<projection>`, for the column in the goal. Never bridge a concrete effect tower or compiled artifact through `withOutput`, `setMach`, `setMeta`, `setWorld`, or another `with*` update using bare `change`, `show`, `rfl`, or `exact`.
- Boundary: A succeeding concrete `getStor` walk can expose this projection mechanism after the effect tower is built. Reuse the shared `Devm.withRefundCounter_getStor` and `Devm.addLog_getStor` cuts with a private cold-store boundary; do not reorder `Meta` fields. This does not reopen `successor-projection-normalization`, and resource ceilings neither detect nor bound this kernel-side cost. The target must expose an explicit `Devm` update head; if a local definition hides it, unfold only that binding and run `blanc_suggest` again. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `devm-projection-bridge`.
- Owner module: [Blanc/LidoCircuitBreakerDeploymentMessage.lean](../Blanc/LidoCircuitBreakerDeploymentMessage.lean)
- Canonical example: [Blanc/LidoCircuitBreakerDeploymentMessage.lean](../Blanc/LidoCircuitBreakerDeploymentMessage.lean) — `officialConstructorPost_refundCounter`
- Registered symbols: `declaration:LidoCircuitBreaker.officialConstructorPost_refundCounter`
- Review: `proof-infrastructure` on `2026-08-25`

## `bytesize-composition`

- Status: `active`
- Triggers: `goal-shape:compileshape-bytesize`
- Preferred path: Prove one small `decide +kernel` fact per leaf, then derive internal `compileShape.byteSize` facts arithmetically through `dispatchNode_size`-style composition. `dispatchCae9_size` is the canonical example: with its children available, its composition closes in 0.004 s.
- Boundary: The measured law is about 2.6 ms per compiled byte of the addressed object; byte-range width predicts nothing because `byteAtByShape` is lazy. Hoist named size facts only for repeated consumers of the same object. Do not generalize the narrower domain-slices route; reopen it only with a broader child-fact or representation change that improves the owning row. Keep `weth10MainEmit_drop_3950` unchanged. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `bytesize-composition`.
- Owner module: [Blanc/Weth10Deploy.lean](../Blanc/Weth10Deploy.lean)
- Canonical example: [Blanc/Weth10DeployUpperSlices.lean](../Blanc/Weth10DeployUpperSlices.lean) — `dispatchCae9_size`
- Registered symbols: `declaration:Weth10.dispatchCae9_size`
- Review: `proof-infrastructure` on `2026-08-25`

## `compiled-shape-byte-navigation`

- Status: `active`
- Triggers: `goal-shape:compiled-shape-byte-navigation`
- Preferred path: Import `Blanc.CompiledShape` and open `CompiledShape` inside `namespace Blanc`. Use `byteAt_next_to_tail` once the index is beyond a reference instruction, even when the executed instruction and tail differ; use `byteAt_prepend_*` for fixed instruction prefixes, `byteAt_branch_*` for branch header/left/jumpdest/right regions, `dispatchNodeByteAt_*` for the common selector-dispatch shape, and `pushFullWord_*` for a fixed 32-byte `Ninst.push`. Supply the existing compile-shape, size, and index-bound facts so the proof traverses only the addressed subtree.
- Boundary: These lemmas navigate `Func.byteAtByShape` from an already supplied compile shape. They do not prove a shape is correct, compile a function, or replace contract-specific selector, route, or closed-size facts. `byteAt_next_to_tail` uses the reference instruction's size for the supplied lower bound and offset; it does not assert that the reference and executed instructions have equal bytes or widths. `pushFullWord_*` applies only to a fixed 32-byte `Ninst.push w.toBytes`; it is not `Ninst.pushB256`, whose immediate width is value-dependent. To avoid recursively normalizing a large closed function, the matcher performs bounded structural inspection: explicit `.next`/`.branch`, direct `Func.next`/`Func.branch` under `compileShape`, and the registered `CompiledShape.dispatchNode` wrapper. Other reducible wrappers should be exposed by the author only as far as the relevant constructor before invoking `blanc_suggest` again.
- Owner module: [Blanc/CompiledShape.lean](../Blanc/CompiledShape.lean)
- Canonical example: [Blanc/CompiledShape.lean](../Blanc/CompiledShape.lean) — `byteAt_branch_to_right`
- Registered symbols: `module:Blanc/CompiledShape.lean`, `declaration:Blanc.CompiledShape.byteAt_next_to_tail`, `declaration:Blanc.CompiledShape.byteAt_prepend_to_tail`, `declaration:Blanc.CompiledShape.byteAt_branch_to_right`, `declaration:Blanc.CompiledShape.dispatchNodeByteAt_to_onPath`, `declaration:Blanc.CompiledShape.pushFullWord_opcode_eq`
- Review: `proof-infrastructure` on `2026-09-09`

## `compiler-structural-composition`

- Status: `active`
- Triggers: `goal-shape:compile-prepend`, `goal-shape:compile-branch`
- Preferred path: Import `Blanc.CompiledShape`. Use `CompiledShape.compile_prepend` or `compile_prepend_of` to retain an opaque continuation, and `compile_branch` to assemble already checked child compilations and a bounded jump target. Use `dispatchLeaf_size` and `prefixByteSize_fsig` for the corresponding shared size facts.
- Boundary: Matches only a direct compiler equality with an explicit `prepend` or `Func.branch` function argument. It does not unfold wrappers, traverse a closed function, search hypotheses, prove child compilations, establish table entries, or discharge jump bounds. Expose one source constructor and supply its checked children and coordinates.
- Owner module: [Blanc/CompiledShape.lean](../Blanc/CompiledShape.lean)
- Canonical example: [Blanc/CompiledShape.lean](../Blanc/CompiledShape.lean) — `compile_prepend_of`
- Registered symbols: `declaration:Blanc.CompiledShape.compile_prepend`, `declaration:Blanc.CompiledShape.compile_prepend_of`, `declaration:Blanc.CompiledShape.compile_branch`, `declaration:Blanc.CompiledShape.dispatchLeaf_size`, `declaration:Blanc.CompiledShape.prefixByteSize_fsig`
- Review: `proof-infrastructure` on `2026-09-20`

## `compile-shape-prepend-congruence`

- Status: `active`
- Triggers: `goal-shape:compile-shape-prepend-congruence`
- Preferred path: For an equality `(l +++ p).compileShape = (l +++ q).compileShape`, apply `Func.compileShape_prepend_congr l` to an existing tail-shape equality `p.compileShape = q.compileShape`.
- Boundary: This transports an already proved compile-shape equality through one syntactically identical instruction-line prefix. It does not prove the tail equality, compare different prefixes, normalize either tail, or search the local context. The matcher requires an `Eq` whose two sides are direct `compileShape` applications to `prepend`, with syntactically identical instantiated prefixes and syntactically distinct tails; no-prepend and reflexive-tail goals stay on the general route.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean) — `Func.compileShape_prepend_congr`
- Registered symbols: `module:Blanc/CommonProofs.lean`, `declaration:Blanc.Func.compileShape_prepend_congr`
- Review: `proof-infrastructure` on `2026-09-09`

## `bounded-creation-word-encoder`

- Status: `active`
- Triggers: `goal-shape:bounded-creation-word-encoder`
- Preferred path: For an exact `Ninst.RunCompiled` goal over `CreationArtifact.pushB256AsPush2OrPush32 word`, apply `Ninst.runCompiled_pushB256AsPush2OrPush32`. Supply `devm.gasLeft = G + gVerylow` and `devm.stack.length < 1024`; the result pushes the same word, preserves memory, and leaves gas `G`.
- Boundary: The encoder's input and operational conclusion are exact `B256` values. A `Nat` consumer must separately prove its value is below `2^256` before conversion. This theorem establishes one instruction's execution; it proves no provisional/final prefix fixed point, constructor execution, or message execution. The matcher inspects only the four-argument `Ninst.RunCompiled` spine and requires the instruction argument itself to have the exact encoder head; it does not traverse the pre-state, result, or closed word, and performs no reduction or normalization.
- Owner module: [Blanc/CreationArtifact.lean](../Blanc/CreationArtifact.lean)
- Canonical example: [Blanc/CreationArtifact.lean](../Blanc/CreationArtifact.lean) — `Ninst.runCompiled_pushB256AsPush2OrPush32`
- Registered symbols: `module:Blanc/CreationArtifact.lean`, `declaration:Blanc.CreationArtifact.pushB256AsPush2OrPush32`, `declaration:Blanc.Ninst.runCompiled_pushB256AsPush2OrPush32`
- Review: `proof-infrastructure` on `2026-09-08`

## `successor-projection-normalization`

- Status: `partial`
- Triggers: `goal-shape:successor-projection`
- Preferred path: Use an existing named, oriented, one-layer projection lemma when one already serves the goal; otherwise keep the explicit local normalization.
- Boundary: Do not replace deep state towers with transparent abbreviations or broad unfolding. The tested one-layer projection retrofit regressed, and later owner analysis found kernel checks dominate the relevant Lido access and Registry work; this does not recommend `setMach`-chain cleanup or a module split. Resource ceilings do not bound this kernel-side cost. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `successor-projection-normalization`.
- Owner module: [Blanc/Forward.lean](../Blanc/Forward.lean)
- Canonical example: [Blanc/Forward.lean](../Blanc/Forward.lean) — `Devm.getStorVal_setMach`
- Registered symbols: `declaration:Devm.getStorVal_setMach`
- Review: `proof-infrastructure` on `2026-08-21`

## `runcompiled-family-compression`

- Status: `partial`
- Triggers: `goal-shape:runcompiled-family-compression`
- Preferred path: When expensive bodies repeat the same post-kernel walk, freeze a committed-row decision rule, factor the body-from-kernel boundary, and preserve the old statements as instantiations. If a one-shot `func_run` needs a local resource ceiling, promote its exact tactic-produced residual states to named theorem boundaries, reducing the chunks as far as needed; compare against the original declarations' limits before rejecting the factorization. Profile the generic, chunks, and instances, run the bare elaboration gate, withhold the generic in an isolated falsifier, and reject any split that materially regresses its owner row or adds a proof-resource ceiling.
- Boundary: Exact proof-copy deletion alone does not predict owner timing. A private body-from-kernel summary is a candidate only when measurements show the owning closure improves and the route removes real repeated work. Cross-module reuse lacks ancestor headroom in the tested family, and the Registry tail is kernel/definitional-equality owned rather than a compression opportunity. Source symmetry alone does not license a timing retrofit. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `runcompiled-family-compression`.
- Owner module: [Blanc/LidoCircuitBreakerUnregisterRegistration.lean](../Blanc/LidoCircuitBreakerUnregisterRegistration.lean)
- Canonical example: [Blanc/LidoCircuitBreakerUnregisterRegistration.lean](../Blanc/LidoCircuitBreakerUnregisterRegistration.lean) — `registerPauser_body_foundZeroOldLast_runCompiled`
- Registered symbols: `declaration:Blanc.LidoCircuitBreaker.registerPauser_stageArgs_runCompiled`
- Review: `proof-infrastructure` on `2026-08-21`

## `shared-subject-kernel-decision`

- Status: `active`
- Triggers: `goal-shape:shared-subject-kernel-decision`
- Preferred path: When several kernel-decidable facts inspect the same expensive closed subject, bind that subject once, decide the facts as one tuple or conjunction, and project the results; alternatively prove one normalized equality and derive the views with `congrArg`.
- Boundary: Apply only when normalization of one identical closed subject dominates every fact. Do not bundle facts about different subjects or use this as a term-size or definitional-equality cure. Attainment bundling is a known losing shape when aliases and conjunction elaboration outweigh the reuse; reopen it only with a shared closed-subject representation that avoids those costs. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `shared-subject-kernel-decision`.
- Owner module: [Blanc/LidoCircuitBreakerSites.lean](../Blanc/LidoCircuitBreakerSites.lean)
- Canonical example: [Blanc/LidoCircuitBreakerSites.lean](../Blanc/LidoCircuitBreakerSites.lean) — `runtimeSourceEffectPcs_official`
- Registered symbols: `declaration:Blanc.LidoCircuitBreaker.runtimeSourceEffectPcs_official`
- Review: `proof-infrastructure` on `2026-08-25`

## `selector-separation`

- Status: `active`
- Triggers: `goal-shape:selector-separation`
- Preferred path: Hoist a reviewed literal separation table ahead of repeated consumers and transport its facts directly.
- Boundary: This route is module-local. It does not establish a cross-domain canonical selector list, `Nodup` theorem, extractor, named simp set, or cross-module placement; no blocking rule may require those designs. `blanc_suggest` misses the literal `SelectorWordNoPrimaryFlow` certificate goal, so consult this recipe manually for that shape. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `selector-separation`.
- Owner module: [Blanc/Weth10SelectorFacts.lean](../Blanc/Weth10SelectorFacts.lean)
- Canonical example: [Blanc/Weth10SelectorFacts.lean](../Blanc/Weth10SelectorFacts.lean) — `Weth10.selector_name_ne_approveSelector`
- Registered symbols: `declaration:Weth10.selector_name_ne_approveSelector`
- Advisory anti-patterns: `local-selector-table`
- Review: `proof-infrastructure` on `2026-08-21`

## `fixed-byte-offsets`

- Status: `active`
- Triggers: `goal-shape:fixed-byte-offset`
- Preferred path: Use `Bytes.sliceD_writeAt` for the whole written window, `Bytes.sliceD_writeAt_inside` for a contained subwindow, and `Bytes.sliceD_writeAt_before` or `Bytes.sliceD_writeAt_after` for disjoint neighboring windows. For a padded slice, use `Bytes.getD_sliceD_of_lt` for an in-range byte or `Bytes.sliceD_sliceD_of_le` for a contained subwindow. Use `Bytes.readWord_writeAt_self` or `Bytes.readWord_writeAt_of_disjoint` for word reads. For adjacent event words use `Bytes.read_two_word_writes_at` or `Mem.read_two_word_writes_at`. For padded or abstract memory, start from `Mem.Wf` and `Mem.Reads`; in scratch decoders, `of_run_mstoreAt_image` and `of_run_loadWordAt_image` advance the stack, image, well-formedness, and state equation together, while `of_run_loadWordAt_logs` preserves event chronology. For exact primitive byte-store inversion use `of_run_mstore8_val` or its known-prefix wrapper `prefix_of_mstore8_val`, and use `of_run_mstore8_state` for the persistent-state equation. For calldata copies with known operands use `prefix_of_calldatacopy_val`. For creation copies use `of_run_codecopy_image`; its lower-level components are `prefix_of_codecopy_val` plus `of_run_codecopy_logs`. For fixed logs use `of_logWith_image`. Keep compiled-emitter `List.drop` equalities local unless a profile proves that a structural helper moves their kernel cost.
- Boundary: These laws cover byte-array writes and fixed-width word reads; they do not make arbitrary compiled-emitter `List.drop` identities a shared API. Reopen the separate emitter-helper route only when the serialized owning-module median improves by the licensed win rule. Experimental history: Blanc commit 0eee78d571e673f37543e4d306608af445065017, `scripts/proof-recipes.toml`, recipe `fixed-byte-offsets`.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean) — `Bytes.readWord_writeAt_of_disjoint`
- Registered symbols: `module:Blanc/CommonProofs.lean`, `declaration:Bytes.getD_sliceD_of_lt`, `declaration:Bytes.sliceD_sliceD_of_le`, `declaration:Bytes.sliceD_writeAt`, `declaration:Bytes.sliceD_writeAt_inside`, `declaration:Bytes.sliceD_writeAt_before`, `declaration:Bytes.sliceD_writeAt_after`, `declaration:Bytes.readWord_writeAt_self`, `declaration:Bytes.readWord_writeAt_of_disjoint`, `declaration:Bytes.read_two_word_writes_at`, `declaration:Mem.Wf`, `declaration:Mem.Reads`, `declaration:Mem.read_two_word_writes_at`, `declaration:of_run_mstoreAt_image`, `declaration:of_run_mstore8_val`, `declaration:prefix_of_mstore8_val`, `declaration:of_run_mstore8_state`, `declaration:of_run_loadWordAt_image`, `declaration:of_run_loadWordAt_logs`, `declaration:prefix_of_calldatacopy_val`, `declaration:of_run_codecopy_image`, `declaration:prefix_of_codecopy_val`, `declaration:of_run_codecopy_logs`, `declaration:of_logWith_image`
- Review: `proof-infrastructure` on `2026-08-30`

## `frame-root-carrying-execution`

- Status: `active`
- Triggers: `goal-shape:frame-root-carrying`
- Preferred path: Use `rootedRunCompiledTo` to carry a predicate through a compiled walk, discharge childless instructions with `ninstAllChildRoots_of_not_exec` or `NonExecInstruction`, establish spawning children with `ninstAllChildRoots_of_exec_spawn`, and finish a whole program with `Prog.exec_of_rootedRunCompiledTo`.
- Boundary: This API preserves predicates over raw entered-frame roots. It does not apply settlement/commit filtering; use `ExecutionSettlement` and `ExecutionOccurrence` for retained or committed histories.
- Owner module: [Blanc/RootedExecution.lean](../Blanc/RootedExecution.lean)
- Canonical example: [Blanc/RootedExecution.lean](../Blanc/RootedExecution.lean) — `Prog.exec_of_rootedRunCompiledTo`
- Registered symbols: `module:Blanc/RootedExecution.lean`, `declaration:rootedRunCompiledTo`, `declaration:ninstAllChildRoots`, `declaration:ninstAllChildRoots_of_not_exec`, `declaration:ninstAllChildRoots_of_exec_spawn`, `declaration:funcExecFree`, `declaration:rootedRunCompiledTo_of_execFree`, `declaration:Prog.exec_of_rootedRunCompiledTo`, `declaration:NonExecInstruction`
- Review: `proof-infrastructure` on `2026-08-29`

## `trace-admitted-frame-invariant`

- Status: `active`
- Triggers: `goal-head:ContractSpec.PreservesAdmitted`
- Preferred path: State the target program obligation as `ContractSpec.SoundAdmitted ca entry`, keeping the concrete `Exec.FrameAdmitted` premise result-free, then apply `ContractSpec.preserves_inv_admitted`. Use `Exec.FrameAdmitted.root` at the selected target entry and the named child/continuation restriction lemmas rather than rebuilding raw-frame list membership. When the program proof needs the ordinary message-entry empty stack and memory, conjoin its independent premise with `Exec.FreshEntry` using `Exec.FrameAdmitted.and`; retained wrappers derive the fresh half through their `freshFrameAdmitted` theorem. Drop to `preserves_lift_admitted` or `lift_inv_admitted` only when the standard `ContractSpec.PreWf` carrier is insufficient.
- Boundary: Admission ranges over raw actually entered frame roots and is not a settlement filter or a postcondition. `freshFrameAdmitted` certifies only empty stack and memory from actual entered frames; it does not manufacture an environment, storage, delegation, or precompile fact. The caller must establish every independent entry premise for the concrete execution or retained trace; this recipe does not weaken `PreservesAdmitted` to an endpoint premise or replace the forward `RootedExecution` construction API.
- Owner module: [Blanc/ContractAdmission.lean](../Blanc/ContractAdmission.lean)
- Canonical example: [Blanc/ContractAdmission.lean](../Blanc/ContractAdmission.lean) — `ContractSpec.preserves_inv_admitted`
- Registered symbols: `module:Blanc/ExecutionFrames.lean`, `module:Blanc/ExecutionFrameEntry.lean`, `module:Blanc/ExecutionAdmission.lean`, `module:Blanc/ContractAdmission.lean`, `declaration:Blanc.Exec.FrameAdmitted`, `declaration:Blanc.Exec.FrameAdmitted.root`, `declaration:Blanc.Exec.FreshEntry`, `declaration:Blanc.Exec.FrameAdmitted.and`, `declaration:Blanc.ForallSubExecAdmitted`, `declaration:Blanc.lift_admitted`, `declaration:Blanc.lift_inv_admitted`, `declaration:Blanc.ContractSpec.SoundAdmitted`, `declaration:Blanc.ContractSpec.PreservesAdmitted`, `declaration:Blanc.ContractSpec.preserves_lift_admitted`, `declaration:Blanc.ContractSpec.preserves_inv_admitted`
- Review: `proof-infrastructure` on `2026-09-01`

## `message-execution-settlement`

- Status: `active`
- Triggers: `goal-shape:message-execution-settlement`
- Preferred path: The message-execution adapters and message-entry projections are Jaune's (`Jaune.MessageExecution`, imported through `Blanc/MessageExecution.lean`; Blanc opens `Jaune`, so the short names below resolve). Use `MessageExecution.processMessage_eq_settle_exec_of_enter` when an exact successful `Frame.enter` equation is already retained, including for delegated children. For payable ordinary calls, derive a normal non-precompile entry with `executeCode_enter_of_codeAddress_not_precompile` and use the `*_afterTransfer_of_codeEntry` adapters; the `*_afterTransfer_of_notPrecompile` bridge packages the same route from address evidence. Use `processMessage_eq_settle_exec_afterTransfer_of_noCodeAddress` for creation-code entry, or `processMessage_eq_settle_exec_afterTransfer` when precompiles are explicitly disabled. Then use the clean/revert/halt adapters and canonical `settledRevert` or `settledHalt` machines instead of unfolding message settlement at the contract site. Use the unsuffixed adapters for the identity-entry specialization. For an already-retained `ProcessMessage`, use Blanc's `MessageExecution.processMessage_clean_rawPost` to recover the successful raw post, `processMessage_entry_facts` for the actual entry frame projections, and the separate `processMessage_entry_stack` / `processMessage_entry_memory` empty-entry projections. For an actual retained zero-value static-precompile child whose routing already selected the native precompile, use `stor_of_processMessage_staticPrecomp`; at address `0x2` on exactly 64 input bytes, use `gasSha25664_le_of_processMessage_clean`, `output_of_processMessage_sha256_64_clean`, or their combined `frame_of_processMessage_sha256_64_clean` image.
- Boundary: The generic enter bridge requires only the exact successful entry equation. Post-transfer bridges name the successful transferred environment: exact-code-entry and non-precompile variants work with ordinary `disablePrecompiles = false` messages, the no-code-address variant covers creation code, and the convenience bridge requires disabled precompiles. The unsuffixed specialization additionally requires entry-state identity. Retained-frame inversion exposes storage equality rather than whole-state equality because value transfer may change balances. Static-precompile inversion does not prove native routing: its enabled-precompile and clean-child premises remain load-bearing, delegation must already be ruled out, and the SHA result is fixed only for address 2 and exactly 64 bytes. These facts describe ordinary call-message settlement, not CREATE settlement.
- Owner module: [Blanc/MessageExecutionInversion.lean](../Blanc/MessageExecutionInversion.lean)
- Canonical example: [Blanc/MessageExecutionInversion.lean](../Blanc/MessageExecutionInversion.lean) — `MessageExecution.processMessage_clean_rawPost`
- Registered symbols: `module:Blanc/MessageExecution.lean`, `module:Blanc/MessageExecutionInversion.lean`, `module:Blanc/StaticPrecompileMessage.lean`, `declaration:MessageExecution.processMessage_clean_rawPost`, `declaration:MessageExecution.processMessage_entry_facts`, `declaration:MessageExecution.processMessage_entry_stack`, `declaration:MessageExecution.processMessage_entry_memory`, `declaration:Blanc.stor_of_processMessage_staticPrecomp`, `declaration:Blanc.gasSha25664_le_of_processMessage_clean`, `declaration:Blanc.output_of_processMessage_sha256_64_clean`, `declaration:Blanc.frame_of_processMessage_sha256_64_clean`
- Review: `proof-infrastructure` on `2026-09-01`

## `raw-sstore-free-compiled-path`

- Status: `active`
- Triggers: `goal-shape:raw-sstore-free-compiled-path`
- Preferred path: Build `Func.RunCompiledTo.NoRawSstorePath` over the exact selected compiled derivation, supplying childlessness for every reached external instruction. Use `NoRawSstorePath.of_entrySstoreFree_reachableExecFree` when the executable finite-component checkers prove both local SSTORE freedom and reachable exec freedom; otherwise use `NoRawSstorePath.of_execFree` for an execution-free, locally SSTORE-free body, `NoRawSstorePath.of_prepend_nonexec` for an instruction-only prefix, `NoRawSstorePath.of_revertWith` for a symbolic constant-error body, or `NoRawSstorePath.of_emptyRevertGuard` for a selected nonzero guard calling an empty-revert auxiliary. When a failing prefix is checker-safe only with a harmless success continuation, certify that source and use `NoRawSstorePath.replaceStopWith_of_error` to reinstate the production continuation that the exact error path never enters; `Func.replaceStopWith_prepend` normalizes an instruction-only prefix around that replacement. For a warm fixed-width SHA-256 precompile step, preserve the empty child slot with `Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext`; finish with `Prog.exists_exec_noRawSstore`. When an exact `Exec` already exists, use `Exec.noRawSstore_of_exactMain_entrySstoreFree_reachableExecFree` to combine the two executable entry certificates occurrence-first.
- Boundary: This is raw construction-direction chronology, not rollback reasoning. An empty retained-write list or reverted terminal state does not prove the certificate because an earlier raw SSTORE may have executed and then rolled back. Entered child frames require their own evidence; synchronously resolved childless precompiles may use the explicit done-frame constructor.
- Owner module: [Blanc/ForwardNoRawSstore.lean](../Blanc/ForwardNoRawSstore.lean)
- Canonical example: [Blanc/ForwardNoRawSstore.lean](../Blanc/ForwardNoRawSstore.lean) — `Func.RunCompiledTo.NoRawSstorePath.of_execFree`
- Registered symbols: `module:Blanc/ForwardNoRawSstore.lean`, `declaration:Blanc.Ninst.ChildlessRunCompiled`, `declaration:Blanc.Ninst.ChildlessRunCompiled.toRunCompiled`, `declaration:Blanc.Ninst.childlessRunCompiled_exec_doneFrame`, `declaration:Blanc.Ninst.childlessRunCompiled_staticcall_doneFrame`, `declaration:Blanc.Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext`, `declaration:Blanc.emptyRevertGuardCost`, `declaration:Blanc.Func.runCompiledTo_emptyRevertGuard`, `declaration:Blanc.Exec.NoRawSstore`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_execFree`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_revertWith`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_emptyRevertGuard`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_prepend_nonexec`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_entrySstoreFree_reachableExecFree`, `declaration:Blanc.Func.replaceStopWith`, `declaration:Blanc.Func.replaceStopWith_prepend`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.replaceStopWith_of_error`, `declaration:Blanc.Prog.exists_exec_noRawSstore`, `declaration:Blanc.Exec.noRawSstore_of_exactMain_entrySstoreFree_reachableExecFree`, `declaration:Blanc.Exec.NoRawSstore.no_successfulSstoreOccurrence`, `declaration:Blanc.Exec.NoRawSstore.retainedStorageWrites_eq_nil`, `declaration:Blanc.Exec.NoRawSstore.retainedStorageEffectTriples_eq_nil`
- Review: `proof-infrastructure` on `2026-08-30`

## `retained-write-noninterference`

- Status: `active`
- Triggers: `goal-shape:retained-write-noninterference`
- Preferred path: For `Exec.NoRetainedWriteTo`, split first on `Execution.commits out = true`. Close the rollback arm with `Exec.noRetainedWriteTo_of_not_commits`; on a committing exact-main invocation use `Exec.noRetainedWriteTo_of_exactMain_reachableExecFree` when the selected entry and its finite internal-call component pass `Prog.reachableExecFree`. For a dispatcher-selected non-main entry, route an actual `SourceCursor` through `Toward.linearDispatchWith_selectedBody`, discharge same-frame exec absence with `SourceCursor.noExec_of_reachableExecFree`, and finish with `Exec.noRetainedWriteTo_of_no_sameFrame_execAt`. Whole-program source-childlessness and entered-frame owner separation remain the other committing routes.
- Boundary: The noncommitting theorem proves retained-write absence by rollback, not raw instruction absence. `Prog.reachableExecFree` checks both arms and a finite lookup-resolved call-closed source component, but says nothing about unselected entries, child outcomes, commitment, gas, or liveness. The exact-main endpoint applies only to `program.main`; a selected dispatcher body needs the explicit actual-route cursor bridge. Do not infer childlessness merely from a static call flag.
- Owner module: [Blanc/ExecutionNoninterference.lean](../Blanc/ExecutionNoninterference.lean)
- Canonical example: [Blanc/ExecutionNoninterference.lean](../Blanc/ExecutionNoninterference.lean) — `Exec.noRetainedWriteTo_of_not_commits`
- Registered symbols: `module:Blanc/ExecutionNoninterference.lean`, `declaration:Exec.NoRetainedWriteTo`, `declaration:Exec.noRetainedWriteTo_of_not_commits`, `declaration:Exec.noRetainedWriteTo_of_no_execOccurrence`, `declaration:Exec.noRetainedWriteTo_of_sourceSites_no_exec`, `declaration:Exec.noRetainedWriteTo_of_frame_owners_ne`, `module:Blanc/ReachableExecFree.lean`, `declaration:Prog.reachableExecFree`, `declaration:Prog.reachableExecFree_iff`, `declaration:Exec.Deriv.SourceCursor.Toward.linearDispatchWith_selectedBody`, `declaration:Exec.Deriv.SourceCursor.noExec_of_reachableExecFree`, `declaration:Exec.noRetainedWriteTo_of_no_sameFrame_execAt`, `declaration:Exec.noRetainedWriteTo_of_exactMain_reachableExecFree`
- Review: `proof-infrastructure` on `2026-08-30`

## `exact-retained-storage-effects`

- Status: `active`
- Triggers: `goal-shape:exact-retained-storage-effects`
- Preferred path: For a committing selected compiled walk, build `Func.RunCompiledTo.StorageEffectPath` in source order. For a long construction that must thread the indexed run and annotation together, use `Func.StorageEffectRun` and its source-shaped constructors; `next_effectNeutral` preserves the tail list across an ordinary non-SSTORE step, while `of_noRawSstorePath` packages an existing empty selected-path certificate. Its `.run` projection recovers the exact indexed `Func.RunCompiledTo` witness without rebuilding the selected walk. Use `storage_effect_run` to walk a childless neutral prefix with the `func_run` state/gas/hint engine; it hands external instructions, SSTOREs, internal calls, and terminals back to the caller. To replace a designated successful STOP with an exact-effect continuation, certify the selected neutral walk with `RunCompiledTo.SuccessfulStopPrefix.of_execFree` and apply `SuccessfulStopPrefix.splice`. Convert an existing raw-SSTORE-free certificate with `StorageEffectPath.of_noRawSstorePath`; convert an exact empty annotation back to raw freedom with `StorageEffectPath.noRawSstorePath_of_nil` or `StorageEffectRun.noRawSstorePath`. Otherwise supply `Ninst.ChildlessRunCompiled` at each synchronously resolved external step. Finish with `Prog.exists_exec_retainedStorageEffectTriples`, or `_appended` when the compiled program is only the exact prefix of a larger creation-code image. When composing an `Exec` directly, use `Exec.retainedStorageEffectTriples_cont`, `Exec.retainedStorageEffectTriples_doneOk`, and `Exec.retainedStorageEffectTriples_halt`.
- Boundary: The certificate is exact retained chronology, including successful no-op SSTOREs. It requires a committing successful result and explicit childlessness at external steps; it does not infer child-frame absence from same-frame source classification or final storage equality. The `.run` projection preserves the certificate's exact compiled-run indices; it does not convert an arbitrary source `Func.Run` into compiled evidence.
- Owner module: [Blanc/ForwardStorageEffects.lean](../Blanc/ForwardStorageEffects.lean)
- Canonical example: [Blanc/ForwardStorageEffects.lean](../Blanc/ForwardStorageEffects.lean) — `Prog.exists_exec_retainedStorageEffectTriples`
- Registered symbols: `module:Blanc/ForwardStorageEffects.lean`, `declaration:Blanc.Ninst.storageEffectTriple?`, `declaration:Blanc.Func.RunCompiledTo.StorageEffectPath`, `declaration:Blanc.Func.RunCompiledTo.StorageEffectPath.next_of_not_exec`, `declaration:Blanc.Func.RunCompiledTo.StorageEffectPath.of_noRawSstorePath`, `declaration:Blanc.Func.RunCompiledTo.StorageEffectPath.noRawSstorePath_of_nil`, `declaration:Blanc.Func.StorageEffectRun`, `declaration:Blanc.Func.StorageEffectRun.of_noRawSstorePath`, `declaration:Blanc.Func.StorageEffectRun.noRawSstorePath`, `declaration:Blanc.Func.StorageEffectRun.last`, `declaration:Blanc.Func.StorageEffectRun.next`, `declaration:Blanc.Func.StorageEffectRun.next_effectNeutral`, `declaration:Blanc.Func.StorageEffectRun.zero`, `declaration:Blanc.Func.StorageEffectRun.succ`, `declaration:Blanc.Func.StorageEffectRun.call`, `declaration:Blanc.Func.storageEffectRun_branch_zero`, `declaration:Blanc.Func.storageEffectRun_branch_succ`, `declaration:Blanc.Func.SuccessStopOnly`, `declaration:Blanc.Func.RunCompiledTo.SuccessfulStopPrefix`, `declaration:Blanc.Func.RunCompiledTo.SuccessfulStopPrefix.of_execFree`, `declaration:Blanc.Func.RunCompiledTo.SuccessfulStopPrefix.splice`, `declaration:Blanc.Prog.exists_exec_retainedStorageEffectTriples`, `declaration:Blanc.Prog.exists_exec_retainedStorageEffectTriples_appended`, `declaration:Blanc.Exec.retainedStorageEffectTriples_cont`, `declaration:Blanc.Exec.retainedStorageEffectTriples_doneOk`, `declaration:Blanc.Exec.retainedStorageEffectTriples_halt`
- Review: `proof-infrastructure` on `2026-08-30`

## `binary-dispatch-miss`

- Status: `active`
- Triggers: `goal-shape:raw-sstore-free-compiled-path`
- Preferred path: For an unmatched selector in a `DispatchTree`, prove `¬ tree.HasSelector selector` and apply `DispatchTree.dispatchMiss_runCompiledTo_with_path`. The result is the exact selector-dependent empty-revert `RunCompiledTo` paired with `NoRawSstorePath` for that identical proof; `DispatchTree.dispatchMissGas` names its exact cost.
- Boundary: This follows only the selected miss path. It does not inspect or certify unselected sibling bodies, prove a contract-specific selector census, or add the selector-extraction and program-main prefix around `dispatch tree`.
- Owner module: [Blanc/ForwardDispatchMiss.lean](../Blanc/ForwardDispatchMiss.lean)
- Canonical example: [Blanc/ForwardDispatchMiss.lean](../Blanc/ForwardDispatchMiss.lean) — `DispatchTree.dispatchMiss_runCompiledTo_with_path`
- Registered symbols: `module:Blanc/ForwardDispatchMiss.lean`, `declaration:Blanc.DispatchTree.HasSelector`, `declaration:Blanc.DispatchTree.dispatchMissGas`, `declaration:Blanc.DispatchTree.dispatchMiss_runCompiledTo_with_path`
- Review: `proof-infrastructure` on `2026-08-31`

## `accepted-boolean-settlement`

- Status: `active`
- Triggers: `goal-shape:accepted-bool-word`
- Preferred path: For a clean full-word ABI output, use `acceptedBoolWord_iff_of_output` instead of repeating the slice/read normalization. Remove a successful execution wrapper with `acceptedBoolExecution_ok_iff`, and specialize rejected-answer executions with `boolQueryExecutionFailure_ok_iff`.
- Boundary: These adapters identify one already-clean 32-byte boolean observation. They do not prove message settlement, output production, or that the returned word is canonical zero or one.
- Owner module: [Blanc/PinnedPauseTarget.lean](../Blanc/PinnedPauseTarget.lean)
- Canonical example: [Blanc/PinnedPauseTarget.lean](../Blanc/PinnedPauseTarget.lean) — `acceptedBoolWord_iff_of_output`
- Registered symbols: `module:Blanc/PinnedPauseTarget.lean`, `declaration:acceptedBoolWord_iff_of_output`, `declaration:acceptedBoolExecution_ok_iff`, `declaration:boolQueryExecutionFailure_ok_iff`
- Review: `proof-infrastructure` on `2026-08-30`

## `devm-common-update-laws`

- Status: `active`
- Triggers: `goal-shape:devm-common-update-law`
- Preferred path: Before proving a record projection by `rfl`, search the public `Devm` laws in `CommonProofs`: memory writes, accessed-storage/setMach cancellation, storage/code read-after-write, code-installation observations, and the reusable RETURN/SSTORE post projection cuts are named there. For Solidity address-typed storage, use `addressSlotReadWord`/`addressSlotWriteWord` and the value-carrying `loadAddressWordAt`/`storeAddressWordAt` inversions rather than restating mask algebra locally. Jaune also supplies update-first projection laws such as `Devm.memWrite_gasLeft` and `Devm.setMach_accessedStorageKeys`.
- Boundary: Use the smallest abstract-base law that matches the goal. Do not unfold a concrete effect tower merely because these laws themselves are definitionally simple.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean) — `Devm.addAccessedStorageKey_setMach_setMach`
- Registered symbols: `module:Blanc/CommonProofs.lean`, `declaration:Devm.memWrite_memory`, `declaration:Devm.memWrite_stack`, `declaration:Devm.addAccessedStorageKey_setMach_setMach`, `declaration:Devm.getStorVal_setStorVal_self`, `declaration:Devm.setStorVal_getCode`, `declaration:Devm.setCode_logs`, `declaration:Devm.setCode_output`, `declaration:Devm.setCode_error`, `declaration:Devm.returnPost_getStorVal`, `declaration:Devm.returnPost_accessedStorageKeys`, `declaration:Devm.sstoreBase_state`, `declaration:Devm.sstoreBase_accessedStorageKeys`, `declaration:Devm.sstoreWarmBase_accessedStorageKeys`, `module:Blanc/AddressSlot.lean`, `module:Blanc/AddressSlotProofs.lean`, `declaration:addressSlotReadWord`, `declaration:addressSlotWriteWord`, `declaration:addressSlotReadWord_eq_toAdr_toB256`, `declaration:of_loadAddressWordAt_val`, `declaration:of_storeAddressWordAt_val`
- Review: `proof-infrastructure` on `2026-08-30`

## `compiled-terminal-at-zero`

- Status: `active`
- Triggers: `goal-shape:terminal-return-revert`
- Preferred path: For an offset-zero 32-byte RETURN or empty REVERT, use `Func.runCompiledTo_return_word_at_zero` or `Func.runCompiledTo_revert_empty_at_zero`; use the more general `Func.runCompiledTo_return_word` and `Func.runCompiledTo_revert` only when the offset, size, stack tail, or payload differs.
- Boundary: These are construction lemmas for two common terminal shapes, not inversion theorems and not a replacement for the general terminal APIs.
- Owner module: [Blanc/ExecutionTerminal.lean](../Blanc/ExecutionTerminal.lean)
- Canonical example: [Blanc/ExecutionTerminal.lean](../Blanc/ExecutionTerminal.lean) — `Func.runCompiledTo_return_word_at_zero`
- Registered symbols: `module:Blanc/ExecutionTerminal.lean`, `declaration:Func.runCompiledTo_return_word_at_zero`, `declaration:Func.runCompiledTo_revert_empty_at_zero`
- Review: `proof-infrastructure` on `2026-08-29`

## `full-length-slice`

- Status: `active`
- Triggers: `goal-shape:full-length-slice`
- Preferred path: When a padded `sliceD` begins at zero and its requested width is the source length, rewrite with `Bytes.sliceD_zero_length` instead of reproving the take/drop normalization locally.
- Boundary: The theorem needs exact equality between source length and requested width. It does not characterize nonzero offsets or shorter/longer windows.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean) — `Bytes.sliceD_zero_length`
- Registered symbols: `module:Blanc/CommonProofs.lean`, `declaration:Bytes.sliceD_zero_length`
- Review: `proof-infrastructure` on `2026-08-29`

## `retained-wrapper-trace`

- Status: `active`
- Triggers: `goal-shape:retained-wrapper-trace`
- Preferred path: Choose the carrier at the wrapper boundary you actually have, then use its matching `exists_*Trace` theorem to retain Jaune's deterministic recursive witness. Start with `RetainedXlot` for a filled execution slot; use `ProcessMessageTrace.result` or `ProcessCreateMessageTrace.result` to recover the exact deterministic core-wrapper equation. At a retained delegated-child boundary, use `DelegatecallSpawnDescriptor.certificate_of_runCompiled` to invert an existing successful compiled step into its arbitrary child outcome and resume equation, `DelegatecallSpawnDescriptor.runCompiled_of_certificate` to construct the exact compiled step from such a child plus its resume equation, or `.settled_of_runCompiled` to retain the settled child together with exact parent observations. Then use `DelegatedChildCertificate.process`, `.result`, or `.rollback_of_error` for the retained child. Use `MessageCallTrace`, `TransactionTrace`, `AppliedBodyTrace`, or the configured block/history carriers instead of reconstructing a trace from only the terminal state.
- Boundary: These carriers remember execution and wrapper structure but assign no contract-specific meaning to effects. Use the `Execution*Effects` modules for `ContractSpec` transport, `ExecutionPath` for stable call-tree locations, and the `Execution*StateTrace` modules for ordered world-state replay.
- Owner module: [Blanc/ExecutionTrace.lean](../Blanc/ExecutionTrace.lean)
- Canonical example: [Blanc/ExecutionTrace.lean](../Blanc/ExecutionTrace.lean) — `ExecutionTrace.exists_messageCallTrace`
- Registered symbols: `module:Blanc/ExecutionTrace.lean`, `module:Blanc/ExecutionHistory.lean`, `module:Blanc/DelegatecallEnvelope.lean`, `declaration:ExecutionTrace.RetainedXlot`, `declaration:ExecutionTrace.exists_retainedXlot_of_filled`, `declaration:ExecutionTrace.ProcessMessageTrace`, `declaration:ExecutionTrace.exists_processMessageTrace`, `declaration:ExecutionTrace.ProcessMessageTrace.result`, `declaration:ExecutionTrace.ProcessCreateMessageTrace`, `declaration:ExecutionTrace.exists_processCreateMessageTrace`, `declaration:ExecutionTrace.ProcessCreateMessageTrace.result`, `declaration:ExecutionTrace.MessageCallTrace`, `declaration:ExecutionTrace.exists_messageCallTrace`, `declaration:DelegatedChildCertificate`, `declaration:DelegatecallSpawnDescriptor.certificate_of_runCompiled`, `declaration:DelegatecallSpawnDescriptor.runCompiled_of_certificate`, `declaration:DelegatecallSettledBoundary`, `declaration:DelegatecallSpawnDescriptor.settled_of_runCompiled`, `declaration:DelegatedChildCertificate.process`, `declaration:DelegatedChildCertificate.result`, `declaration:DelegatedChildCertificate.rollback_of_error`, `declaration:ExecutionTrace.TransactionTrace`, `declaration:ExecutionTrace.exists_transactionTrace`, `declaration:ExecutionTrace.ApplyTransactionsTrace`, `declaration:ExecutionTrace.exists_applyTransactionsTrace`, `declaration:ExecutionTrace.SystemMessageTrace`, `declaration:ExecutionTrace.exists_systemMessageTrace`, `declaration:ExecutionTrace.RequestsTrace`, `declaration:ExecutionTrace.exists_requestsTrace`, `declaration:ExecutionTrace.AppliedBodyTrace`, `declaration:ExecutionTrace.exists_appliedBodyTrace`, `declaration:ExecutionTrace.ConfiguredBlockTrace`, `declaration:ExecutionTrace.exists_configuredBlockTrace_of_transition`, `declaration:ExecutionTrace.ConfiguredHistoryTrace`, `declaration:ExecutionTrace.exists_configuredHistoryTrace_of_reachUsing`
- Review: `proof-infrastructure` on `2026-08-30`

## `trace-local-frame-admission`

- Status: `active`
- Triggers: `goal-shape:trace-local-frame-admission`
- Preferred path: State the contract's entry condition as `Exec.FrameAdmitted ca entry` on the exact retained execution. Prove the frame obligation as `ContractSpec.SoundAdmitted ca entry`, close it with `ContractSpec.preserves_inv_admitted`, and use the matching `FrameAdmitted` plus `stateInv_admitted`/`benvInv_admitted` theorem on `MessageCallTrace`, `TransactionTrace`, `AppliedBodyTrace`, or `ConfiguredHistoryTrace` to transport it through only the interpreter frames actually entered. If the proof also needs canonical interpreter ingress, obtain `Exec.FreshEntry` from the carrier's `freshFrameAdmitted` theorem and combine it with the independent admission through the carrier's `FrameAdmitted.and`.
- Boundary: Admission is evidence about concrete target-frame roots, not an execution constructor, settlement filter, or global environment restriction. Fresh-entry transport contributes only empty stack and memory and cannot discharge independent routing or world-state premises. The consumer must derive those premises from the retained trace; rollback and direct envelope effects remain governed by the ordinary wrapper transports.
- Owner module: [Blanc/ExecutionAdmission.lean](../Blanc/ExecutionAdmission.lean)
- Canonical example: [Blanc/ExecutionHistoryAdmission.lean](../Blanc/ExecutionHistoryAdmission.lean) — `ExecutionTrace.ConfiguredHistoryTrace.stateInv_admitted`
- Registered symbols: `module:Blanc/ExecutionFrames.lean`, `module:Blanc/ExecutionFrameEntry.lean`, `module:Blanc/ExecutionAdmission.lean`, `module:Blanc/ContractAdmission.lean`, `module:Blanc/ExecutionMessageAdmission.lean`, `module:Blanc/ExecutionTransactionAdmission.lean`, `module:Blanc/ExecutionBodyAdmission.lean`, `module:Blanc/ExecutionHistoryAdmission.lean`, `module:Blanc/ExecutionTraceFresh.lean`, `declaration:Exec.FrameAdmitted`, `declaration:Exec.FreshEntry`, `declaration:Exec.FrameAdmitted.and`, `declaration:ExecutionTrace.ConfiguredHistoryTrace.FrameAdmitted.and`, `declaration:ExecutionTrace.ConfiguredHistoryTrace.freshFrameAdmitted`, `declaration:lift_inv_admitted`, `declaration:ContractSpec.SoundAdmitted`, `declaration:ContractSpec.PreservesAdmitted`, `declaration:ContractSpec.preserves_inv_admitted`, `declaration:ExecutionTrace.MessageCallTrace.stateInv_admitted`, `declaration:ExecutionTrace.TransactionTrace.benvInv_admitted`, `declaration:ExecutionTrace.AppliedBodyTrace.stateInv_admitted`, `declaration:ExecutionTrace.ConfiguredHistoryTrace.stateInv_admitted`
- Review: `proof-infrastructure` on `2026-09-01`

## `retained-state-replay`

- Status: `active`
- Triggers: `goal-head:StateReplay`
- Preferred path: Build the chronology at the narrowest retained layer and finish with its `stateReplay` theorem. Use `Exec.committedStateReplay` for a recursive execution, then the message, transaction, body, block, or history chronology module to retain wrapper boundaries in their exact execution order. Compose or relabel an existing replay with `StateReplay.append`, `StateReplay.mapOrigin`, and `StateTransition.mapOrigin`.
- Boundary: A `StateReplay` proves endpoint continuity and preserves exact provenance; it does not classify a transition as a contract deposit, withdrawal, or attack step. Apply that interpretation only in the contract-owned layer above the generic chronology.
- Owner module: [Blanc/ExecutionStateTrace.lean](../Blanc/ExecutionStateTrace.lean)
- Canonical example: [Blanc/ExecutionStateTrace.lean](../Blanc/ExecutionStateTrace.lean) — `Exec.committedStateReplay`
- Registered symbols: `module:Blanc/ExecutionStateTrace.lean`, `module:Blanc/ExecutionMessageStateTrace.lean`, `module:Blanc/ExecutionTransactionStateTrace.lean`, `module:Blanc/ExecutionBodyStateTrace.lean`, `module:Blanc/ExecutionHistoryStateTrace.lean`, `declaration:StateTransition`, `declaration:StateReplay`, `declaration:StateReplay.append`, `declaration:StateTransition.mapOrigin`, `declaration:StateReplay.mapOrigin`, `declaration:Exec.committedStateReplay`, `declaration:ExecutionTrace.MessageCallTrace.stateReplay`, `declaration:ExecutionTrace.TransactionStateChronology.stateReplay`, `declaration:ExecutionTrace.AppliedBodyStateChronology.stateReplay`, `declaration:ExecutionTrace.ConfiguredHistoryStateChronology.stateReplay`
- Review: `proof-infrastructure` on `2026-08-30`

## `constant-error-guard`

- Status: `active`
- Triggers: `goal-shape:constant-error-guard`
- Preferred path: Use `Func.runCompiledTo_errorGuard` when a nonzero branch flag tail-calls an auxiliary equal to `Func.revertWith reason`. Supply the auxiliary lookup, exact entry-state memory image and alignment, payload bounds, gas expressed through `errorGuardCost`, and stack room; the theorem returns the complete ABI `Error(string)` payload with exact final memory, stack, and gas. When an existential carrier exposes a different state with the same memory size, transport that exact cost with `errorGuardCost_congr_memory_size`.
- Boundary: This proves the branch-and-internal-call walk only. It does not select a contract route, establish which flag is nonzero, authenticate a contract-specific reason/slot table, or turn the local revert into a public endpoint theorem. Keep `errorGuardCost` indexed by the actual entry state, or transport it only across a proved memory-size equality, so memory expansion is not silently weakened.
- Owner module: [Blanc/RevertPayload.lean](../Blanc/RevertPayload.lean)
- Canonical example: [Blanc/RevertPayload.lean](../Blanc/RevertPayload.lean) — `Func.runCompiledTo_errorGuard`
- Registered symbols: `module:Blanc/RevertPayload.lean`, `declaration:Blanc.errorBodyCost`, `declaration:Blanc.errorCallCost`, `declaration:Blanc.errorGuardCost`, `declaration:Blanc.errorGuardCost_congr_memory_size`, `declaration:Blanc.Func.runCompiledTo_revertWith`, `declaration:Blanc.Func.runCompiledTo_errorGuard`
- Review: `proof-infrastructure` on `2026-08-30`

## `one-word-source-return`

- Status: `active`
- Triggers: `goal-head:ReturnsWord`
- Preferred path: For the source fragment `mstoreAt 0 +++ returnMemoryRange 0 32`, use `of_storeReturnWord` when a `Mem.Wf`/`Mem.Reads` image is already available, or `returnsWord_of_storeReturn` when no memory side condition is in context. Both prove `ReturnsWord` from the known stack head and preserve code.
- Boundary: This is the source-level one-word ABI observation. For a compiled terminal walk use `Func.runCompiledTo_return_word_at_zero`; for other offsets, sizes, or payloads use the general return APIs.
- Owner module: [Blanc/LadderBase.lean](../Blanc/LadderBase.lean)
- Canonical example: [Blanc/LadderBase.lean](../Blanc/LadderBase.lean) — `returnsWord_of_storeReturn`
- Registered symbols: `module:Blanc/LadderBase.lean`, `declaration:ReturnsWord`, `declaration:of_storeReturnWord`, `declaration:returnsWord_of_storeReturn`
- Review: `proof-infrastructure` on `2026-08-30`

## `upgrade-migration-refinement`

- Status: `active`
- Triggers: `goal-head:MigrationSound`, `goal-head:BehavioralRefinement`
- Preferred path: Start from `UpgradeArchitecture`, keeping `proxyProg`, v1, v2, the migration, and the relation explicit. Prove `MigrationSound` from the named state transformer independently of `BehavioralRefinement`; then prove the latter from version-specific shared steps. A product theorem must separately connect an exact proxy execution to the migration.
- Boundary: These predicates describe a migration and shared logical behavior. They do not execute a proxy, establish authorization or installation, transport a child through delegatecall, prove rollback, or turn one predicate into evidence for the other.
- Owner module: [Blanc/Upgrade.lean](../Blanc/Upgrade.lean)
- Canonical example: [Blanc/Upgrade.lean](../Blanc/Upgrade.lean) — `MigrationSound`
- Registered symbols: `module:Blanc/Upgrade.lean`, `declaration:Blanc.UpgradeArchitecture`, `declaration:Blanc.MigrationSound`, `declaration:Blanc.BehavioralRefinement`
- Review: `proof-infrastructure` on `2026-09-01`

## `memory-window-transport`

- Status: `active`
- Triggers: `goal-head:MemWordAt`, `goal-head:MemImage`, `implication-premise:MemWordAt`
- Preferred path: A long-lived memory word that must survive unrelated scratch traffic is carried by the shared proof-carrying window in `Blanc/MemoryImage.lean`; import it with `import Blanc.MemoryImage` and do not declare a contract-local survival predicate. Use `MemImage` while the proof still needs the whole reader image, then drop to `MemWordAt` as soon as only one 32-byte window matters. For several writes, import `Blanc/MemoryLayout.lean` and state one ordered `MemoryStage`: `applyImage` and `applyMemory` fold the actual primitives in the listed order, `wf_reads` proves their correspondence, and `footprint` retains exact byte spans. Use the decidable `avoids`/`avoidsAll` guards for preserved padded windows and `read_written` when only later writes must miss the selected payload; use `words`, `applyMemory_words_size`, and `read_written_word` for word stores. When a hashed or observed region spans more than one staged write, join the per-window readbacks with `List.sliceD_add` (`Blanc/BytesWrite.lean`); for the adjacent-word case, `Mem.read_two_word_writes_at` gives the readback directly. `MemImage.applyStage`, `MemWordAt.applyStage`, and `MemoryStage.wordFrameFrom` bridge the finite stage back to the existing carriers. For one write or an execution boundary, continue with `writeMiss`/`writeMissBytes`, `extend`/`extends`, `extendsWrite`, the `across*` family, and `Bytes.WordFrameFrom`. `Blanc/BeaconDepositAbiMemory.lean:depositDecodedMemory_carrier` is the ordered fresh-layout example; `Blanc/BeaconDepositConstructorStorageEffects.lean:constructorPairWindow_storageEffectRun` remains the single-write scratch example.
- Boundary: Stage order is semantic: overlapping writes are not sorted or commuted, and `read_written` constrains only its later suffix. `footprint` is an exact byte-span list, while `applyMemory_size` uses `memExtsSize`; neither `avoids` nor byte coverage implies an unrounded allocation equation. `applyMemory_size_of_covered` therefore requires every write to fit the initial allocated size. Empty payloads, padding, extension and word byte order stay those of `Mem.write`, `Bytes.writeAt`, and `B256.toBytes`. The execution transport theorems remain frame-shaped and prove nothing about what a step computed; their disjointness and call-relation premises stay at the call site. These small structural proofs do not justify a raised `maxRecDepth` or `maxHeartbeats` scope.
- Owner module: [Blanc/MemoryImage.lean](../Blanc/MemoryImage.lean)
- Canonical example: [Blanc/LidoCircuitBreakerPauseJoin.lean](../Blanc/LidoCircuitBreakerPauseJoin.lean) — `responder_hcall`
- Registered symbols: `module:Blanc/MemoryImage.lean`, `module:Blanc/MemoryLayout.lean`, `declaration:Blanc.MemImage`, `declaration:Blanc.MemImage.write`, `declaration:Blanc.MemWordAt`, `declaration:Blanc.MemWordAt.of_memImage`, `declaration:Blanc.MemWordAt.memImage`, `declaration:Blanc.MemWordAt.readWord`, `declaration:Blanc.MemWordAt.of_write`, `declaration:Blanc.MemWordAt.writeMiss`, `declaration:Blanc.MemWordAt.writeMissBytes`, `declaration:Blanc.MemWordAt.extend`, `declaration:Blanc.MemWordAt.extends`, `declaration:Blanc.MemWordAt.extendsWrite`, `declaration:Blanc.MemWordAt.acrossLine`, `declaration:Blanc.MemWordAt.acrossNinst`, `declaration:Blanc.MemWordAt.acrossStaticcall`, `declaration:Blanc.MemWordAt.acrossSuccessfulCall`, `declaration:Blanc.Bytes.WordFrameFrom`, `declaration:Blanc.Bytes.WordFrameFrom.writeBefore`, `declaration:Blanc.Bytes.WordFrameFrom.sliceD`, `declaration:Blanc.MemWordAt.of_wordFrame`, `declaration:Blanc.prefix_of_loadWord_window`, `declaration:Blanc.of_run_mstoreAt_mem`, `declaration:Blanc.MemoryStage.applyImage`, `declaration:Blanc.MemoryStage.applyMemory`, `declaration:Blanc.MemoryStage.footprint`, `declaration:Blanc.MemoryStage.avoids`, `declaration:Blanc.MemoryStage.applyImage_sliceD_of_avoids`, `declaration:Blanc.MemoryStage.read_written`, `declaration:Blanc.MemoryStage.wf_reads`, `declaration:Blanc.MemoryStage.applyMemory_size`, `declaration:Blanc.MemImage.applyStage`, `declaration:Blanc.MemWordAt.applyStage`
- Review: `proof-infrastructure` on `2026-09-09`

## `operand-stack-certificate`

- Status: `active`
- Triggers: `goal-head:CompiledStackSafety.StepSafe`, `goal-head:CompiledStackSafety.Certificate`, `goal-shape:operand-stack-fault-free`
- Preferred path: Absence of an operand-stack fault over fixed compiled bytes is a checked finite table, not a hand-rolled per-contract height counter. Import the chain with `import Blanc.AbstractStackCertificate`. For a real compiled artifact, feed its evaluator-emitted bytes and an explicit maximum to the untrusted `scripts/stack_certificate.py` producer, then discharge the generated table with `checkTable_certificate` applied to one `decide` of `checkTable code table maximum = true`; `python3 scripts/gen-proxy-pair-stack-certificate.py` is the complete compiler-bound check and `--write` is its writer. The four declarations at the end of `Blanc/AbstractStackCertificate.lean` — `exampleCode`, `exampleTable`, `exampleTable_checked`, `exampleTable_certificate` — remain the minimal handwritten use. Transport the resulting `Certificate` over the actual same-frame chronology with `Certificate.parentStep`, `Certificate.parentPrefix` and `Certificate.at_parentPrefix`; they reuse `Exec.Deriv.ParentPrefix` rather than introducing a parallel execution relation. Generated named packs still check successors against the complete table; compose separately proved pieces with `Table.all_node`, and use `Table.count_le_one` or `Table.checkLayout` only when row uniqueness or a contiguous layout is separately wanted. `docs/COMMON_API.md` section E9 is the need-first entry point.
- Boundary: The Python producer is explicitly untrusted data preparation: only the unchanged Lean `checkTable` against the actual code supplies certificate evidence. Its balanced 15-row leaf size is a representation boundary inherited from the DRIP donor, not an optimization claim. The conclusion is local and same-frame. It states that every reached same-frame node satisfies the checked invariant and that no step generates a `StackFault`; it proves nothing about gas, liveness, termination, whether any program counter is reached, or the code of a spawned child frame. A CALL's child is arbitrary: only the parent's resumption is covered, and a stack fault arriving through the child settlement is attributed by `InheritedStackFault`, not excluded. The accepted family is narrow and fails closed to `false` on everything else — `regularTransfer` covers ADD, MUL, SUB, DIV, LT, GT, EQ, ISZERO, AND, SHR, CALLER, CALLVALUE, CALLDATALOAD, CALLDATASIZE, TIMESTAMP, POP, MLOAD, MSTORE, SLOAD, SSTORE, GAS, DUP and SWAP; CALL is the only accepted external instruction; SELFDESTRUCT is rejected. `checkTable` hard-caps the stack ceiling at `maximum ≤ 8`, which is the limit of the proved transfer family rather than a tuning knob: raising it requires new transfer theorems, not a larger literal. Validation is one kernel `decide` over the tree, so its cost grows with row count and pattern width and a very large table should be split with `Table.all_node`. The tree shape supplies no trusted premise — a wrong tree fails `Table.checkOrder` or a row check instead of weakening the theorem.
- Owner module: [Blanc/AbstractStackCertificate.lean](../Blanc/AbstractStackCertificate.lean)
- Canonical example: [Blanc/AbstractStackCertificate.lean](../Blanc/AbstractStackCertificate.lean) — `exampleTable_certificate`
- Registered symbols: `module:Blanc/AbstractStackCertificate.lean`, `module:Blanc/AbstractStackTransfer.lean`, `module:Blanc/AbstractStackSafety.lean`, `module:Blanc/CompiledStackSafety.lean`, `declaration:Blanc.CompiledStackSafety.StackFault`, `declaration:Blanc.CompiledStackSafety.NoStackFault`, `declaration:Blanc.CompiledStackSafety.InheritedStackFault`, `declaration:Blanc.CompiledStackSafety.ResumeSafe`, `declaration:Blanc.CompiledStackSafety.StepSafe`, `declaration:Blanc.CompiledStackSafety.Certificate`, `declaration:Blanc.CompiledStackSafety.Certificate.parentStep`, `declaration:Blanc.CompiledStackSafety.Certificate.parentPrefix`, `declaration:Blanc.CompiledStackSafety.Certificate.at_parentPrefix`, `declaration:Blanc.AbstractStackSafety.Pattern`, `declaration:Blanc.AbstractStackSafety.Matches`, `declaration:Blanc.AbstractStackSafety.SafeResult`, `declaration:Blanc.AbstractStackSafety.regularTransfer`, `declaration:Blanc.AbstractStackSafety.terminalTransfer`, `declaration:Blanc.AbstractStackSafety.callTransfer`, `declaration:Blanc.AbstractStackSafety.Table`, `declaration:Blanc.AbstractStackSafety.Table.Invariant`, `declaration:Blanc.AbstractStackSafety.Table.all_node`, `declaration:Blanc.AbstractStackSafety.Table.count_le_one`, `declaration:Blanc.AbstractStackSafety.Table.checkLayout`, `declaration:Blanc.AbstractStackSafety.checkTable`, `declaration:Blanc.AbstractStackSafety.checkTable_certificate`, `declaration:Blanc.AbstractStackSafety.exampleTable_checked`, `declaration:Blanc.AbstractStackSafety.exampleTable_certificate`
- Review: `proof-infrastructure` on `2026-09-07`

## `finite-coalition-ledger`

- Status: `active`
- Triggers: `goal-shape:finite-coalition-ledger`
- Preferred path: Import `Blanc.LedgerConservation` and express the observation as `ledgerSumOn coalition balances`. Use `ledgerSumOn_congr` for pointwise equality, `ledgerSumOn_increase` for an actual `Increase` plus receiver-row `B256.Nof`, `ledgerSumOn_decrease` for an actual `Decrease` plus owner cover, and `ledgerSumOn_transfer` for an actual `Transfer` plus pre-state `SumNof`. The transfer theorem handles a self-transfer and every coalition-membership overlap; do not split them into an owner-not-receiver side condition.
- Boundary: These are local finite-coalition equations. An `Increase` alone permits receiver-side word wrap, a `Decrease` needs cover, and a `Transfer` needs pre-state `SumNof`; prove those facts at the operation boundary. Neither the equations nor `LedgerConserved` establish configured-history admission, an actual endpoint run, or path-level preservation.
- Owner module: [Blanc/LedgerConservation.lean](../Blanc/LedgerConservation.lean)
- Canonical example: [Blanc/LedgerConservation.lean](../Blanc/LedgerConservation.lean) — `ledgerSumOn_transfer`
- Registered symbols: `module:Blanc/LedgerConservation.lean`, `declaration:Blanc.ledgerSumOn`, `declaration:Blanc.ledgerSumOn_congr`, `declaration:Blanc.ledgerSumOn_increase`, `declaration:Blanc.ledgerSumOn_decrease`, `declaration:Blanc.ledgerSumOn_transfer`, `declaration:Blanc.LedgerConserved.sumNof`
- Review: `proof-infrastructure` on `2026-09-16`

## `symbolic-label-linking`

- Status: `active`
- Triggers: `goal-shape:symbolic-label-linking`, `goal-head:LinkCertificate`
- Preferred path: A large auxiliary call table is linked by name through `Blanc/SymbolicProgram.lean`, not by hand-maintained numeric targets. Author the program as `SymbolicProg Label` whose `SymbolicFunc.call` carries a label, then prove `resolve p = .ok (p.erase map)` with `resolve_eq_erase_of_callsOk`: its two premises are `SymbolicProg.validateDefinitions p = .ok ()`, normally `rfl`, and `SymbolicProg.callsOk p map = true`, one `decide +kernel` over the closed `SymbolicProg.allCalls` list. That front end is the route to use when `Label` is an infinite type (a label carrying a `Nat` coordinate), where agreement is not total and `cases target <;> rfl` is unavailable; use `resolve_eq_erase` directly when the label type is finite and agreement is total. For the converse direction `erase_eq_of_resolve` is harder to use than its one-line mention suggests: its agreement premise is *total* over `Label`, and `cases target <;> simp_all` does not close it because `simp` will not unfold `SymbolicProg.findLabel?` through a structure literal and leaves one `0 = n`-shaped goal per label — prove the per-label `findLabel?` equations separately, each `rfl`, add a `findLabel? = none` equation for every label the table does not define, and pass them all to `simp_all` explicitly, as `workedProg_erase_of_resolve` does. Pin individual coordinates with `SymbolicProg.findLabel?` equations and bound the table with a `findLabel? = none` negative control, as `LidoTriggerableWithdrawalsGateway.symbolicRuntime_findLabel_base_out_of_range` does. Lift an existing numeric `Func` with the shared `Func.mapCalls` and its erasure law `Func.erase_mapCalls_eq_mapTargets` (corollaries `Func.erase_mapCalls`, `Func.erase_mapCalls_of_inverse`) instead of writing a per-contract four-arm structural recursion; `Func.toSymbolic?`/`Func.liftCallFree` are the deliberately different call-rejecting sibling whose erasure `Func.erase_liftCallFree` is a side-condition-free `simp` lemma. Reuse `symbolicLinearDispatchWith` and `erase_symbolicLinearDispatchWith` for a symbolic selector chain. At a `LinkCertificate sp` goal, supply `resolved`, `resolve_eq` and `compiles` over the existing production `Prog`, leaving that definition exactly as it was, rather than re-anchoring it on a certificate projection and moving every downstream `unfold`/`simp` normal form; `checkLink` is the decision form and `LinkCertificate.bytes`, `compile_eq`, `isSome_compile`, `length_compile`, `table_get_root` and `table_get_aux` are the compiled-artifact interface. `docs/COMMON_API.md` section C6 is the need-first entry point; `LidoCircuitBreaker.symbolicLinkCert` and `LidoTriggerableWithdrawalsGateway.symbolicLinkCert` are the production consumers, each against a thousand-line runtime. The minimal working example is `workedProg` in the owner module's `Control` section: `workedProg_resolve : resolve workedProg = .ok workedNumbered` against a hand-numbered `Prog` written out in full, with both premises, the per-label `findLabel?` coordinates, two `findLabel? = none` bounds, the separate `workedProg_auxLabels` order statement, the `erase_eq_of_resolve` discharge and `workedProg_checkLink`. Copy that one; `nestedBranch_checkLink`, `selfRecursion_checkLink` and `mutualRecursion_checkLink` beside it prove only `(checkLink _).isOk = true` and demonstrate nothing that transports.
- Boundary: Resolution is a coordinate assignment and linking is a compiler witness. Neither states anything about the semantics of the erased program: no `Func.Run`, `Func.RunCompiled`, gas, execution outcome, storage effect, selector route or ABI fact follows from a `LinkCertificate`, and those obligations remain ordinary work about the `Prog` that `resolve` returns. The usage rule that follows from this, and not a caveat to it: a bare `LinkCertificate` transports nothing, because all it gives you is `resolve p = .ok cert.resolved` — an equation against a `Prog` you never wrote down and have proved nothing about. Gas and execution facts transport only when you write the numeric `Prog` out by hand and prove `resolve p = .ok <that program>` against it, at which point the agreement is not proved here but made vacuous by syntactic identity, both sides being the same term, which is exactly what lets a gas or run fact about the hand-numbered program rewrite across it. A consumer that keeps only a certificate has linked its table and transported nothing. `resolve_eq_erase_of_callsOk` needs both halves and neither is implied by the other — `SymbolicProg.validateDefinitions` is only the definition domain (no root reuse in the table, no duplicate auxiliary labels including unused duplicates) and the decidable `SymbolicProg.callsOk` is agreement between the table and `map` restricted to the call targets that actually occur, not total agreement, which is false for an infinite `Label`. Because erasure discards labels, an erasure theorem alone does not catch a reordered table, and this is a separate load-bearing statement rather than a detail: state the label list on its own, as `workedProg_auxLabels` and `LidoTriggerableWithdrawalsGateway.symbolicBaseAux_labels` do. Compilability is `checkLink`'s second half and nothing in `resolve` implies it; a call target at or above `2 ^ 16` compiles to nothing, pinned exactly by `call_target_65535_compiles` and `call_target_65536_rejects`. Cost: `resolve`, `erase` and the erasure lemmas are structural and cheap and `callsOk` is meant for one `decide +kernel` over a closed call list, but do not put `checkLink` or `resolve` of a production-sized program under a decision procedure, because that forces kernel evaluation of `Prog.compile` over the whole table. The matcher reads declaration names in the target: `goal-shape:symbolic-label-linking` needs `resolve`, `checkLink`, `SymbolicProg.findLabel?`, `SymbolicProg.validateDefinitions`, `SymbolicProg.callsOk`, `SymbolicProg.erase` or `SymbolicFunc.erase` to be visible, and `goal-head:LinkCertificate` needs `LinkCertificate` to head the goal, so unfold only the local binding that hides one and invoke `blanc_suggest` again.
- Owner module: [Blanc/SymbolicProgram.lean](../Blanc/SymbolicProgram.lean)
- Canonical example: [Blanc/SymbolicProgram.lean](../Blanc/SymbolicProgram.lean) — `workedProg_resolve`
- Registered symbols: `module:Blanc/SymbolicProgram.lean`, `declaration:Blanc.SymbolicFunc`, `declaration:Blanc.SymbolicProg`, `declaration:Blanc.ResolveError`, `declaration:Blanc.SymbolicProg.validateDefinitions`, `declaration:Blanc.SymbolicProg.findLabel?`, `declaration:Blanc.SymbolicProg.erase`, `declaration:Blanc.SymbolicFunc.erase`, `declaration:Blanc.SymbolicProg.allCalls`, `declaration:Blanc.SymbolicProg.callsOk`, `declaration:Blanc.resolve`, `declaration:Blanc.resolve_eq_erase`, `declaration:Blanc.resolve_eq_erase_of_callsOk`, `declaration:Blanc.erase_eq_of_resolve`, `declaration:Blanc.Func.mapCalls`, `declaration:Blanc.Func.erase_mapCalls_eq_mapTargets`, `declaration:Blanc.Func.erase_mapCalls`, `declaration:Blanc.Func.erase_mapCalls_of_inverse`, `declaration:Blanc.Func.toSymbolic?`, `declaration:Blanc.Func.liftCallFree`, `declaration:Blanc.Func.erase_liftCallFree`, `declaration:Blanc.symbolicLinearDispatchWith`, `declaration:Blanc.erase_symbolicLinearDispatchWith`, `declaration:Blanc.checkLink`, `declaration:Blanc.checkLink_isOk`, `declaration:Blanc.checkLink_eq_error_compileFailed`, `declaration:Blanc.LinkError`, `declaration:Blanc.LinkCertificate`, `declaration:Blanc.LinkCertificate.bytes`, `declaration:Blanc.LinkCertificate.compile_eq`, `declaration:Blanc.LinkCertificate.isSome_compile`, `declaration:Blanc.LinkCertificate.length_compile`, `declaration:Blanc.LinkCertificate.table_get_root`, `declaration:Blanc.LinkCertificate.table_get_aux`, `declaration:Blanc.Control.workedProg`, `declaration:Blanc.Control.workedMap`, `declaration:Blanc.Control.workedNumbered`, `declaration:Blanc.Control.workedProg_resolve`, `declaration:Blanc.Control.workedProg_auxLabels`, `declaration:Blanc.Control.workedProg_erase_of_resolve`, `declaration:Blanc.Control.workedProg_checkLink`
- Advisory anti-patterns: `hand-numbered-auxiliary-call-table`, `certificate-kept-without-hand-numbered-program`, `runtime-redefined-as-certificate-projection`, `decide-over-production-sized-checklink`
- Review: `proof-infrastructure` on `2026-09-10`
