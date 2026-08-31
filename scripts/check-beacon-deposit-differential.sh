#!/usr/bin/env bash
# Execute the pinned deployed beacon-deposit runtime and Blanc's evaluated
# runtime through the clean pinned EELS Prague interpreter.  This gate is
# offline and fail-closed: it never fetches EELS, rewrites reference inputs,
# or invents an artifact when the Lean evaluator is absent.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
EELS_ROOT="${EELS_ROOT:-$HOME/execution-specs}"
EELS_PY="$EELS_ROOT/venv/bin/python"
ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS"' EXIT

# This wrapper independently owns the public matrix contract.  The Python
# runner must agree before Lean or EELS execution, so a self-consistent
# weakening in the generator alone cannot silently redefine the gate.
WRAPPER_SCHEMA=3
WRAPPER_CHANNELS="status,returndata,state-projection,eth,logs,sha-staticcall"
WRAPPER_TAGS="selector-deposit,selector-get-deposit-root,selector-get-deposit-count,selector-supports-interface,no-match,malformed-abi,abi-reordered-tails-accepted,abi-overlapping-tails-accepted,abi-dirty-padding-accepted,abi-trailing-data-accepted,abi-all-tails-structural-before-source-guard,nonpayable-root-value,nonpayable-count-value,nonpayable-supports-value,guard-01-invalid-pubkey,guard-02-invalid-withdrawal-credentials,guard-03-invalid-signature,guard-04-value-too-low,guard-05-value-not-gwei,guard-06-value-too-high,guard-07-root-mismatch,guard-08-cap,guard-precedence,value-edge-ether-minus-one,value-edge-one-ether,value-edge-ether-plus-one,value-edge-next-gwei,value-edge-uint64-max,value-edge-above-uint64,chained-counts,root-readback,count-readback,byte-exact-log,byte-exact-revert,sha-staticcall-trace,disabled-precompile-failed-payload,disabled-precompile-failed-empty,disabled-precompile-failed-long,disabled-precompile-short-success,disabled-precompile-long-success-first-word,sha-output-buffer-trace,oog-common-gas-before-first-call,oog-common-gas-child-failure,oog-common-gas-first-success,seeded-cap-layouts,gas-recorded-every-path"
WRAPPER_CHANNEL_FALSIFIERS=6
WRAPPER_MANIFEST_FALSIFIERS=16
WRAPPER_STATIC_FALSIFIERS=4
WRAPPER_CREATION_EXECUTIONS=2
WRAPPER_CREATION_SHA_CALLS=31
WRAPPER_CODE_DEPOSIT_GAS_PER_BYTE=200
WRAPPER_PRAGUE_PRECOMPILE_COUNT=17
WRAPPER_CREATION_ASSERTIONS="executionCount,successfulExecutionCount,shaCallsPerExecution,shaCallsTotal,returnedRuntimeMatchesOwnArtifact,installedRuntimeMatchesOwnArtifact,exactAccountPostState,exactRawStoragePostState,exactLogicalPostState,settledCreatedAccountsEmpty,refundCountersZero"
WRAPPER_CREATION_ASSERTION_CLAIMS="executionCount=2,successfulExecutionCount=2,shaCallsPerExecution=31,shaCallsTotal=62,returnedRuntimeMatchesOwnArtifact=true,installedRuntimeMatchesOwnArtifact=true,exactAccountPostState=true,exactRawStoragePostState=true,exactLogicalPostState=true,settledCreatedAccountsEmpty=true,refundCountersZero=true"
WRAPPER_CREATION_COMPARISON_CHANNELS="semanticShaTraceAgreement,logicalPostStateAgreement,ethAgreement"
WRAPPER_CREATION_COMPARISON_CLAIMS="semanticShaTraceAgreement=true,logicalPostStateAgreement=true,ethAgreement=true,shaOutputOffsetEqualityClaim=false,returnedRuntimeEqualityClaim=false,installedRuntimeEqualityClaim=false,rawStorageEqualityClaim=false"
WRAPPER_CREATION_GAS_KEYS="createMessageGas,codeDepositGas,constructorExecutionGas"
WRAPPER_CREATION_DOMINANCE_KEYS="createMessageGas,constructorExecutionGas"
WRAPPER_CREATION_MESSAGE_BASIS="entry=direct process_message_call,target=0x,currentTarget=0x00000000219ab540356cbb839cbe05303d7705fa,caller=0x1111111111111111111111111111111111111111,callerNonce=1,callerBalance=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,gasLimit=20000000,value=0x0,data=0x,codeAddress=null,depth=0,shouldTransferValue=true,isStatic=false,disablePrecompiles=false,freshStatePerSide=true,targetInitiallyAbsent=true"
WRAPPER_CREATION_PREWARM_POLICY="transactionAccessListAddresses=[],transactionAccessListStorageKeys=[],"\
"initialMessageAccessedAddresses=[0x0000000000000000000000000000000000000001|0x0000000000000000000000000000000000000002|0x0000000000000000000000000000000000000003|0x0000000000000000000000000000000000000004|0x0000000000000000000000000000000000000005|0x0000000000000000000000000000000000000006|0x0000000000000000000000000000000000000007|0x0000000000000000000000000000000000000008|0x0000000000000000000000000000000000000009|0x000000000000000000000000000000000000000a|0x000000000000000000000000000000000000000b|0x000000000000000000000000000000000000000c|0x000000000000000000000000000000000000000d|0x000000000000000000000000000000000000000e|0x000000000000000000000000000000000000000f|0x0000000000000000000000000000000000000010|0x0000000000000000000000000000000000000011|0x00000000219ab540356cbb839cbe05303d7705fa|0x1111111111111111111111111111111111111111|0x2222222222222222222222222222222222222222],"\
"initialMessageAccessedStorageKeys=[],"\
"praguePrecompileAddresses=[0x0000000000000000000000000000000000000001|0x0000000000000000000000000000000000000002|0x0000000000000000000000000000000000000003|0x0000000000000000000000000000000000000004|0x0000000000000000000000000000000000000005|0x0000000000000000000000000000000000000006|0x0000000000000000000000000000000000000007|0x0000000000000000000000000000000000000008|0x0000000000000000000000000000000000000009|0x000000000000000000000000000000000000000a|0x000000000000000000000000000000000000000b|0x000000000000000000000000000000000000000c|0x000000000000000000000000000000000000000d|0x000000000000000000000000000000000000000e|0x000000000000000000000000000000000000000f|0x0000000000000000000000000000000000000010|0x0000000000000000000000000000000000000011],"\
"allPraguePrecompilesPrewarmed=true,coinbasePrewarmed=true"
WRAPPER_CREATION_GAS_BOUNDARY="basis=gas supplied at the direct prepared creation-message boundary,"\
"included=[constructor EVM execution including 31 native SHA-256 child calls|successful runtime code-deposit charge],"\
"excluded=[transaction intrinsic base and creation surcharge|transaction calldata zero/nonzero-byte charges|EIP-3860 initcode-word charge|transaction calldata-floor settlement|transaction refund application],"\
"refundTreatment=direct message gas is measured before transaction refund application; both successful constructors must report refund counter zero,gasEqualityClaim=false"
WRAPPER_ARGS=(
  --wrapper-schema "$WRAPPER_SCHEMA"
  --wrapper-channels "$WRAPPER_CHANNELS"
  --wrapper-tags "$WRAPPER_TAGS"
  --wrapper-channel-falsifiers "$WRAPPER_CHANNEL_FALSIFIERS"
  --wrapper-manifest-falsifiers "$WRAPPER_MANIFEST_FALSIFIERS"
  --wrapper-static-falsifiers "$WRAPPER_STATIC_FALSIFIERS"
  --wrapper-creation-executions "$WRAPPER_CREATION_EXECUTIONS"
  --wrapper-creation-sha-calls "$WRAPPER_CREATION_SHA_CALLS"
  --wrapper-code-deposit-gas-per-byte "$WRAPPER_CODE_DEPOSIT_GAS_PER_BYTE"
  --wrapper-prague-precompile-count "$WRAPPER_PRAGUE_PRECOMPILE_COUNT"
  --wrapper-creation-assertions "$WRAPPER_CREATION_ASSERTIONS"
  --wrapper-creation-assertion-claims "$WRAPPER_CREATION_ASSERTION_CLAIMS"
  --wrapper-creation-comparison-channels "$WRAPPER_CREATION_COMPARISON_CHANNELS"
  --wrapper-creation-comparison-claims "$WRAPPER_CREATION_COMPARISON_CLAIMS"
  --wrapper-creation-gas-keys "$WRAPPER_CREATION_GAS_KEYS"
  --wrapper-creation-dominance-keys "$WRAPPER_CREATION_DOMINANCE_KEYS"
  --wrapper-creation-message-basis "$WRAPPER_CREATION_MESSAGE_BASIS"
  --wrapper-creation-prewarm-policy "$WRAPPER_CREATION_PREWARM_POLICY"
  --wrapper-creation-gas-boundary "$WRAPPER_CREATION_GAS_BOUNDARY"
)

if [ ! -x "$EELS_PY" ]; then
  echo "REGRESSION — beacon-deposit differential: pinned EELS python not found at $EELS_PY" >&2
  exit 1
fi

if ! PYTHONDONTWRITEBYTECODE=1 "$EELS_PY" \
  "$SCRIPT_DIR/gen-beacon-deposit-differential.py" \
  --static-self-check "${WRAPPER_ARGS[@]}"; then
  echo "REGRESSION — beacon-deposit differential: wrapper/Python matrix contract failed" >&2
  exit 1
fi

if ! (cd "$ROOT" && lake env lean \
  scripts/eval-beacon-deposit-differential-code.lean \
  >"$ARTIFACTS" 2>"$ERRORS"); then
  cat "$ERRORS" >&2
  echo "REGRESSION — beacon-deposit differential: Blanc artifact evaluation failed" >&2
  exit 1
fi

PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$EELS_ROOT/src" "$EELS_PY" \
  "$SCRIPT_DIR/gen-beacon-deposit-differential.py" \
  --eels-root "$EELS_ROOT" --blanc-artifacts "$ARTIFACTS" \
  "${WRAPPER_ARGS[@]}" "$@"
