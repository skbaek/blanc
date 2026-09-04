#!/bin/bash
# BeaconDeposit's bounded consumer of the contract-neutral BPO2 lane.  This
# wrapper independently owns the row/channel/profile/dominance contract, gets
# exact artifacts from the Lean evaluator, and gives Python no ambient package
# path or virtual environment.  It has no fork option.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
: "${HOME:?HOME is required}"

WRAPPER_SCHEMA=2
WRAPPER_ROWS="deposit-success,get-deposit-root,get-deposit-count,supports-erc165,supports-deposit,supports-invalid,no-match"
WRAPPER_CHANNELS="status,gas,returndata,deposit-log,deposit-storage,deposit-eth"
WRAPPER_ROW_CHANNEL_MAP="deposit-success=status+gas+returndata+deposit-log+deposit-storage+deposit-eth,get-deposit-root=status+gas+returndata,get-deposit-count=status+gas+returndata,supports-erc165=status+gas+returndata,supports-deposit=status+gas+returndata,supports-invalid=status+gas+returndata,no-match=status+gas+returndata"
WRAPPER_PROFILE_CLAIMS="executionFork=BPO2,executionModule=ethereum.forks.bpo2,chainId=1,reward=-1,logicalCompilerFork=Osaka,testingBackend=cancun,externalSolcInvoked=false"
WRAPPER_DOMINANCE_KEYS="transactionGasUsed,netConstructorExecutionGasAfterRefund"
WRAPPER_CREATION_ASSERTIONS="freshTopLevelTransaction,successfulReceipt,exactCreateTarget,exactInstalledOwnRuntime,exactOwnLayoutStorage,zeroLogs,exactTargetBalanceNonce,eip170RuntimeLimit,eip3860InitcodeLimit,eip7825TransactionGasLimit,refundCounterNotExposed,calldataFloorNotBinding"
WRAPPER_HISTORICAL_BOUNDARY="BPO2 credits status/gas and exact returndata on every row, plus exact deposit log/storage/ETH, reading returndata from the pinned target's own EIP-3155 trace rather than from a receipt, which carries none. The preserved Prague differential still owns the 37 rows outside this seven-row chain and its broader malformed/precompile/OOG corpus; that remainder is measured migration debt recorded in scripts/current-mainnet-parity.json, not a claim that those behaviours cannot have changed across the fork"
WRAPPER_STATIC_FALSIFIERS=4
WRAPPER_API_FALSIFIERS=3
WRAPPER_RAW_CHANNEL_FALSIFIERS=6
WRAPPER_MANIFEST_CHANNEL_FALSIFIERS=5
WRAPPER_REGISTRY_FALSIFIERS=1
WRAPPER_MANIFEST_FALSIFIERS=12
WRAPPER_MANIFEST_CLASSES="row-inventory,credited-channel,profile,constructor-dominance,decomposition-basis,historical-boundary,artifact-size,cache-repository,runtime-lock-path,runtime-lock-digest,cache-ownership,gas-policy"
WRAPPER_DEVIATION_MARKER="beacon-deposit-current-mainnet-gas-v1"
WRAPPER_CREATE_TARGET="0x6295ee1b4f6dd65047762f924ecd367c17eabf8f"
WRAPPER_TX_GAS_LIMIT=16777216
WRAPPER_GAS_CONSTANTS="txBase=21000,txCreate=32000,standardToken=4,floorToken=10,initcodeWord=2,codeDepositPerByte=200,eip170Limit=24576,eip3860Limit=49152"
WRAPPER_CACHE_REPOSITORY_FILES="scripts/current-mainnet-target.json,scripts/current-mainnet-runtime-lock.json,scripts/current_mainnet.py,scripts/gen-current-mainnet-runtime-lock.py,scripts/gen-beacon-deposit-current-mainnet.py,scripts/check-beacon-deposit-current-mainnet.sh,scripts/eval-beacon-deposit-differential-code.lean,scripts/reference/beacon-deposit/inputs/deposit_contract.sol,scripts/reference/beacon-deposit/inputs/deposit_contract.json,scripts/reference/beacon-deposit/inputs/deployed-runtime.norm.hex,BEACON_DEPOSIT_DEVIATIONS.md"
WRAPPER_CACHE_RUNTIME_LOCK="scripts/current-mainnet-runtime-lock.json"
WRAPPER_CACHE_RUNTIME_PLATFORMS="macos-arm64,linux-x86_64"
WRAPPER_CACHE_OWNERSHIP="the shared runtime lock owns exact macOS arm64 and Linux x86_64 native closures; the gate registry additionally fingerprints the selected exact checkout, site-packages population, and CPython 3.11.9 standard library"
WRAPPER_BLANC_ARTIFACTS="runtimeBytes=2891,runtimeSha256=8f2474c60f85dce94e97403369d64d94d7cce4bbb44e620175bd43a5990f0c48,creationBytes=3037,creationSha256=3f3af51d0674c1afb7679dbcc60720bbd3f3d61adc9bd319da025064c0521c59,constructorPrefixBytes=146,constructorSstoreSites=137,constructorStaticcallSites=98,constructorCodecopySites=57"
WRAPPER_ARGS=(
  --wrapper-schema "$WRAPPER_SCHEMA"
  --wrapper-rows "$WRAPPER_ROWS"
  --wrapper-channels "$WRAPPER_CHANNELS"
  --wrapper-row-channel-map "$WRAPPER_ROW_CHANNEL_MAP"
  --wrapper-profile-claims "$WRAPPER_PROFILE_CLAIMS"
  --wrapper-dominance-keys "$WRAPPER_DOMINANCE_KEYS"
  --wrapper-creation-assertions "$WRAPPER_CREATION_ASSERTIONS"
  --wrapper-historical-boundary "$WRAPPER_HISTORICAL_BOUNDARY"
  --wrapper-static-falsifiers "$WRAPPER_STATIC_FALSIFIERS"
  --wrapper-api-falsifiers "$WRAPPER_API_FALSIFIERS"
  --wrapper-raw-channel-falsifiers "$WRAPPER_RAW_CHANNEL_FALSIFIERS"
  --wrapper-manifest-channel-falsifiers "$WRAPPER_MANIFEST_CHANNEL_FALSIFIERS"
  --wrapper-registry-falsifiers "$WRAPPER_REGISTRY_FALSIFIERS"
  --wrapper-manifest-falsifiers "$WRAPPER_MANIFEST_FALSIFIERS"
  --wrapper-manifest-classes "$WRAPPER_MANIFEST_CLASSES"
  --wrapper-deviation-marker "$WRAPPER_DEVIATION_MARKER"
  --wrapper-create-target "$WRAPPER_CREATE_TARGET"
  --wrapper-tx-gas-limit "$WRAPPER_TX_GAS_LIMIT"
  --wrapper-gas-constants "$WRAPPER_GAS_CONSTANTS"
  --wrapper-cache-repository-files "$WRAPPER_CACHE_REPOSITORY_FILES"
  --wrapper-cache-runtime-lock "$WRAPPER_CACHE_RUNTIME_LOCK"
  --wrapper-cache-runtime-platforms "$WRAPPER_CACHE_RUNTIME_PLATFORMS"
  --wrapper-cache-ownership "$WRAPPER_CACHE_OWNERSHIP"
  --wrapper-blanc-artifacts "$WRAPPER_BLANC_ARTIFACTS"
)

STATIC_ENV=(
  "HOME=$HOME"
  "PATH=/usr/bin:/bin:/usr/sbin:/sbin"
  "PYTHONNOUSERSITE=1"
)
if [[ -n "${TMPDIR:-}" ]]; then
  STATIC_ENV+=("TMPDIR=$TMPDIR")
fi

if [[ "${1:-}" == "--static-self-check" ]]; then
  if [[ "$#" -ne 1 ]]; then
    echo "REGRESSION — beacon-deposit current-mainnet: static self-check takes no other arguments" >&2
    exit 1
  fi
  exec /usr/bin/env -i "${STATIC_ENV[@]}" /usr/bin/python3 -B \
    "$SCRIPT_DIR/gen-beacon-deposit-current-mainnet.py" \
    --static-self-check "${WRAPPER_ARGS[@]}"
fi

for argument in "$@"; do
  case "$argument" in
    --write-manifest|--verbose) ;;
    *)
      echo "REGRESSION — beacon-deposit current-mainnet: unsupported wrapper argument $argument" >&2
      exit 1
      ;;
  esac
done

# Refuse a coordinated Python-only weakening before any Lean or target work.
/usr/bin/env -i "${STATIC_ENV[@]}" /usr/bin/python3 -B \
  "$SCRIPT_DIR/gen-beacon-deposit-current-mainnet.py" \
  --static-self-check "${WRAPPER_ARGS[@]}"

if [[ -n "${JAUNE_T8N_TARGET:-}" ]]; then
  TARGET_ROOT="$JAUNE_T8N_TARGET"
else
  TARGET_ROOT="$HOME/execution-specs-t8n-amsterdam"
fi
case "$TARGET_ROOT" in
  "~/"*) TARGET_ROOT="$HOME/${TARGET_ROOT#\~/}" ;;
esac
case "$TARGET_ROOT" in
  /*) ;;
  *)
    echo "REGRESSION — beacon-deposit current-mainnet: target root must be absolute" >&2
    exit 1
    ;;
esac
TARGET_PYTHON="$TARGET_ROOT/.venv/bin/python"
if [[ ! -x "$TARGET_PYTHON" ]]; then
  echo "REGRESSION — beacon-deposit current-mainnet: target Python absent at $TARGET_PYTHON" >&2
  exit 1
fi

ARTIFACTS="$(mktemp)"
ERRORS="$(mktemp)"
trap 'rm -f "$ARTIFACTS" "$ERRORS"' EXIT
if ! (cd "$ROOT" && lake env lean \
  scripts/eval-beacon-deposit-differential-code.lean \
  >"$ARTIFACTS" 2>"$ERRORS"); then
  cat "$ERRORS" >&2
  echo "REGRESSION — beacon-deposit current-mainnet: Blanc artifact evaluation failed" >&2
  exit 1
fi

CHILD_ENV=(
  "HOME=$HOME"
  "PATH=$TARGET_ROOT/.venv/bin:/usr/bin:/bin:/usr/sbin:/sbin"
  "PYTHONNOUSERSITE=1"
  "VIRTUAL_ENV=$TARGET_ROOT/.venv"
)
if [[ -n "${TMPDIR:-}" ]]; then
  CHILD_ENV+=("TMPDIR=$TMPDIR")
fi

exec /usr/bin/env -i "${CHILD_ENV[@]}" "$TARGET_PYTHON" -B -s \
  "$SCRIPT_DIR/gen-beacon-deposit-current-mainnet.py" \
  --root "$TARGET_ROOT" --blanc-artifacts "$ARTIFACTS" \
  "${WRAPPER_ARGS[@]}" "$@"
