#!/usr/bin/env python3
"""Offline EELS differential for Lido TriggerableWithdrawalsGateway.

Both implementations execute their complete CREATE input in a fresh pinned
Prague state.  Runtime histories are compared through an explicit logical
projection; raw storage is never compared.  The five published behavioral
differences are fail-closed, named, and limited to exact fields.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Mapping, NoReturn, Sequence, Tuple

import eels_differential_common as eels


REPO = Path(__file__).resolve().parents[1]
LOCK_PATH = REPO / "scripts" / "lido-twg-reference.json"
CENSUS_PATH = REPO / "scripts" / "lido-twg-census.json"
MANIFEST_PATH = REPO / "scripts" / "fixtures" / "lido-twg" / "manifest.json"
COMPATIBILITY_TOOL = REPO / "scripts" / "lido-twg-compatibility.py"
EELS_PIN = "4198b9c5996713b268aed602739d5aa40e277694"
JAUNE_PIN = "949cf97ee1956828a3ac0eb12a62c438656ba76e"
BLANC_ARTIFACT_COMMIT = "35a196fd50192aa269d6cb07699ea0910ad3c468"
BLANC_PROOF_COMMIT = "a0e04e7a69558b8744ced81ea4a3defdfc478d36"
REFERENCE_WORLD = "differential-corpus"
DEFAULT_GAS_LIMIT = 20_000_000
UINT256_MAX = (1 << 256) - 1
LOW252_MASK = (1 << 252) - 1
REGION_SHIFT = 252

GATEWAY = "0x9999999999999999999999999999999999999999"
CREATE_CALLER = "0x7777777777777777777777777777777777777777"
COINBASE = "0x6666666666666666666666666666666666666666"
ADMIN = "0x111122223333444455556666777788889999aaaa"
LOCATOR = "0x22223333444455556666777788889999aaaabbbb"
VAULT = "0x3333333333333333333333333333333333333333"
ROUTER = "0x4444444444444444444444444444444444444444"
REFUND = "0x5555555555555555555555555555555555555555"
ACTOR = "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
ACTOR_B = "0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
ACTOR_C = "0xcccccccccccccccccccccccccccccccccccccccc"
OTHER = "0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"
REJECTOR = "0xdead00000000000000000000000000000000beef"
ZERO = "0x" + "00" * 20

DEFAULT_ADMIN_ROLE = 0
PAUSE_ROLE = int("139c2898040ef16910dc9f44dc697df79363da767d8bc92f2e310312b816e46d", 16)
RESUME_ROLE = int("2fc10cc8ae19568712f7a176fb4978616a610650813c9d05326c34abb62749c7", 16)
ADD_ROLE = int("15fac8ba7fe8dd5344b88c1915452ce66976f270d1cd793c3b0ab579cecd33c0", 16)
LIMIT_ROLE = int("03c30da9b9e4d4789ac88a294d39a63058ca4a498804c2aa823e381df59d0cf4", 16)

PARAMS = {
    "admin": ADMIN,
    "lidoLocator": LOCATOR,
    "maxExitRequestsLimit": 17,
    "exitsPerFrame": 3,
    "frameDurationInSec": 48,
}
INDEPENDENT_PARAMS = {
    "admin": "0xabcdefabcdefabcdefabcdefabcdefabcdefabcd",
    "lidoLocator": "0x9876598765987659876598765987659876598765",
    "maxExitRequestsLimit": 25,
    "exitsPerFrame": 5,
    "frameDurationInSec": 12,
}

DEVIATION_FIELDS = {
    "TWG-D01": ("returndata",),
    "TWG-D02": ("returndata",),
    "TWG-D03": ("returndata",),
    "TWG-D04": ("returndata", "logicalState"),
    "TWG-D05": ("status", "returndata", "logicalState", "logs"),
}

CHANNEL_FIELDS = {
    "status": ("status",),
    "returndata": ("returndata",),
    "state-projection": ("logicalState", "auxiliaryState"),
    "eth": ("eth",),
    "logs": ("logs",),
    "call-trace": ("callTrace",),
}

GAS_CASES = [
    ("CONSTRUCTOR_SUCCESS", "constructor-success", "constructor-success"),
    ("PAUSE_FOR_FINITE", "pauseFor-finite", "pause-for-finite"),
    ("PAUSE_FOR_SENTINEL", "pauseFor-sentinel", "pause-for-sentinel"),
    ("PAUSE_UNTIL_FINITE", "pauseUntil-finite", "pause-until-finite"),
    ("PAUSE_UNTIL_SENTINEL", "pauseUntil-sentinel", "pause-until-sentinel"),
    ("RESUME", "resume", "resume-authorized"),
    ("IS_PAUSED_FALSE", "isPaused-resumed", "view-is-paused-resumed"),
    ("IS_PAUSED_TRUE", "isPaused-paused", "view-is-paused-paused"),
    ("GRANT_ROLE", "grantRole-fresh", "grant-role-fresh"),
    ("REVOKE_ROLE", "revokeRole-existing", "revoke-role-existing"),
    ("RENOUNCE_ROLE", "renounceRole-self", "renounce-role-self"),
    ("GET_ROLE_MEMBER", "getRoleMember", "get-role-member"),
    ("GET_ROLE_MEMBER_COUNT", "getRoleMemberCount", "get-role-member-count"),
    ("SET_LIMIT", "setExitRequestLimit", "set-limit-valid"),
    ("GET_LIMIT_SAME_FRAME", "getExitRequestLimitFullInfo-same-frame", "get-limit-same-frame"),
    ("GET_LIMIT_REFILLED", "getExitRequestLimitFullInfo-refilled", "get-limit-refilled"),
    ("TRIGGER_EMPTY", "trigger-empty", "trigger-empty"),
    ("TRIGGER_SINGLE_EXACT", "trigger-single-no-refund", "trigger-single-exact-fee"),
    ("TRIGGER_EXPLICIT_REFUND", "trigger-single-explicit-refund", "trigger-explicit-refund"),
    ("TRIGGER_SENDER_REFUND", "trigger-single-sender-refund", "trigger-sender-refund"),
    ("TRIGGER_MULTIPLE", "trigger-multiple", "trigger-multiple"),
    ("TRIGGER_LIMIT", "trigger-limit-exceeded", "trigger-limit-exceeded"),
    ("ROLE_UNAUTHORIZED", "role-gate-unauthorized", "role-negative-pause-for"),
    ("DEFAULT_ADMIN_ROLE_VIEW", "defaultAdminRole", "view-default-admin-role"),
    ("PAUSE_INFINITELY_VIEW", "pauseInfinitely", "view-pause-infinitely"),
    ("SUPPORTS_INTERFACE", "supportsInterface", "view-supports-interface"),
    ("HAS_ROLE", "hasRole", "view-has-role"),
    ("GET_RESUME_TIMESTAMP", "getResumeSinceTimestamp", "view-resume-timestamp"),
    ("GRANT_ROLE_DUPLICATE", "grantRole-duplicate", "grant-role-duplicate"),
    ("REVOKE_ROLE_MISSING", "revokeRole-missing", "revoke-role-missing"),
    ("RENOUNCE_ROLE_WRONG_ACCOUNT", "renounceRole-wrong-account", "renounce-role-wrong-account"),
    ("GET_ROLE_MEMBER_OOB", "getRoleMember-oob", "get-role-member-oob"),
    ("ROLE_ENUMERATION_CROSS_ROLE", "role-enumeration-cross-role-order", "role-enumeration-cross-role-order"),
    ("ROLE_COLLISION_REFUSAL", "role-flat-key-collision-refusal", "role-flat-key-collision-refusal"),
    ("PAUSE_FOR_WHEN_PAUSED", "pauseFor-when-paused", "pause-for-when-paused"),
    ("PAUSE_UNTIL_WHEN_PAUSED", "pauseUntil-when-paused", "pause-until-when-paused"),
    ("PAUSE_ZERO_DURATION", "pauseFor-zero-duration", "pause-zero-duration"),
    ("PAUSE_UNTIL_PAST", "pauseUntil-past", "pause-until-past"),
    ("RESUME_WHEN_RESUMED", "resume-when-resumed", "resume-when-resumed"),
    ("SET_LIMIT_MAX_TOO_LARGE", "setExitRequestLimit-max-too-large", "set-limit-max-too-large"),
    ("SET_LIMIT_FRAME_TOO_LARGE", "setExitRequestLimit-frame-too-large", "set-limit-frame-too-large"),
    ("SET_LIMIT_EXITS_ABOVE_MAX", "setExitRequestLimit-exits-above-max", "set-limit-exits-above-max"),
    ("SET_LIMIT_ZERO_FRAME", "setExitRequestLimit-zero-frame", "set-limit-zero-frame"),
    ("TRIGGER_INSUFFICIENT_FEE", "trigger-insufficient-fee", "trigger-insufficient-fee"),
    ("TRIGGER_PAUSED", "trigger-paused", "trigger-paused"),
    ("TRIGGER_ZERO_VALUE", "trigger-zero-value", "trigger-zero-value"),
    ("TRIGGER_LOCATOR_REVERT", "trigger-locator-revert", "trigger-locator-revert"),
    ("TRIGGER_FEE_QUERY_REVERT", "trigger-fee-query-revert", "trigger-fee-query-revert"),
    ("TRIGGER_VAULT_REVERT", "trigger-vault-revert", "trigger-vault-revert"),
    ("TRIGGER_ROUTER_REVERT", "trigger-router-revert", "trigger-router-revert"),
    ("TRIGGER_REFUND_REVERT", "trigger-refund-revert", "trigger-refund-revert"),
]

RETAINED_NONPOSITIVE_GAS_CASES = {
    "view-is-paused-resumed", "view-is-paused-paused", "role-negative-pause-for",
}

BOUNDARY_DEFINITION = (
    "direct EELS Prague message gas used, computed as message gas minus "
    "output gas_left; constructor rows include code-deposit gas and exclude "
    "transaction intrinsic gas and refunds"
)
PLACEHOLDER_TEMPLATE_DIGESTS = {
    "compatibility": "527ffa4fa5287d020064c254ea877792f5001a20bb091e136c7aeb26bc03150a",
    "deviations": "1e17fa747d0702be780cc42462e4382b9d6fe21232ad180b941a1a898c5833b3",
}
EVENT_TOPICS = {
    "ExitRequestsLimitSet": "0x3119d910326e0f179e121df55f23f45b8a5022ff10c73c02aabf2b48ae36070a",
    "Paused": "0x32fb7c9891bc4f963c7de9f1186d2a7755c7d6e9f4604dabe1d8bb3027c2f49e",
    "Resumed": "0x62451d457bc659158be6e6247f56ec1df424a5c7597f71c20c2bc44e0965c8f9",
    "RoleAdminChanged": "0xbd79b86ffe0ab8e8776151514217cd7cacd52c909f66475c3af44e129f0b00ff",
    "RoleGranted": "0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d",
    "RoleRevoked": "0xf6391f5c32d9c69d2a47ea670b442974b53935d1edc7fd64eb21e047a839171b",
}
CONSTRUCTOR_RETURNDATA = {
    "constructor-admin-zero": "0x6b35b1b7",
    "constructor-max-too-large": "0xaea5046a",
    "constructor-frame-too-large": "0xbbdd2da3",
    "constructor-exits-above-max": "0x528f4863",
    "constructor-zero-frame": "0x6765a75d",
    "constructor-dirty-admin": "0x",
    "constructor-nonpayable": "0x",
}


def die(message: str) -> NoReturn:
    raise RuntimeError(message)


def expect(condition: bool, message: str) -> None:
    if not condition:
        die(message)


def compact(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode()


def digest(value: Any) -> str:
    return hashlib.sha256(compact(value)).hexdigest()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def address_bytes(value: str) -> bytes:
    raw = bytes.fromhex(value.removeprefix("0x"))
    if len(raw) != 20:
        die(f"not an address: {value}")
    return raw


def canonical_address(value: str) -> str:
    return "0x" + address_bytes(value).hex()


def h256(value: int) -> bytes:
    if not 0 <= value <= UINT256_MAX:
        die(f"word outside uint256: {value}")
    return value.to_bytes(32, "big")


def address_word(value: str) -> bytes:
    return bytes(12) + address_bytes(value)


def keccak(data: bytes) -> bytes:
    return bytes(_KECCAK(data))


def selector(signature: str) -> bytes:
    return keccak(signature.encode())[:4]


def calldata(signature: str, *words: int | str | bytes) -> bytes:
    encoded: List[bytes] = []
    for value in words:
        if isinstance(value, str):
            encoded.append(address_word(value))
        elif isinstance(value, int):
            encoded.append(h256(value))
        elif isinstance(value, bytes) and len(value) == 32:
            encoded.append(value)
        else:
            die(f"unsupported ABI word for {signature}")
    return selector(signature) + b"".join(encoded)


def constructor_suffix(params: Mapping[str, object]) -> bytes:
    return b"".join([
        address_word(str(params["admin"])),
        address_word(str(params["lidoLocator"])),
        h256(int(params["maxExitRequestsLimit"])),
        h256(int(params["exitsPerFrame"])),
        h256(int(params["frameDurationInSec"])),
    ])


def trigger_calldata(validators: Sequence[Tuple[int, int, bytes]],
                     recipient: str, exit_type: int) -> bytes:
    heads: List[bytes] = []
    tails: List[bytes] = []
    cursor = 32 * len(validators)
    for module_id, operator_id, pubkey in validators:
        pad = bytes((-len(pubkey)) % 32)
        encoded = h256(module_id) + h256(operator_id) + h256(96) + \
            h256(len(pubkey)) + pubkey + pad
        heads.append(h256(cursor))
        tails.append(encoded)
        cursor += len(encoded)
    array = h256(len(validators)) + b"".join(heads) + b"".join(tails)
    return selector("triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)") + \
        h256(96) + address_word(recipient) + h256(exit_type) + array


def role_hex(role: int) -> str:
    return "0x" + h256(role).hex()


def topic(signature: str) -> str:
    return "0x" + keccak(signature.encode()).hex()


@dataclass(frozen=True)
class Tx:
    caller: str
    calldata: bytes
    value: int = 0
    timestamp: int = 1_700_000_000
    gas: int = DEFAULT_GAS_LIMIT
    target: str = GATEWAY


@dataclass
class Case:
    name: str
    family: str
    selector_signature: str | None = None
    constructor_params: Dict[str, object] = field(default_factory=lambda: dict(PARAMS))
    constructor_suffix_override: bytes | None = None
    constructor_value: int = 0
    constructor_trailing: bytes = b""
    history: List[Tx] = field(default_factory=list)
    action: Tx | None = None
    code: Dict[str, bytes] = field(default_factory=dict)
    observe_roles: List[int] = field(default_factory=list)
    observe_accounts: List[str] = field(default_factory=list)
    observe_aux_slots: Dict[str, int] = field(default_factory=dict)
    tags: Tuple[str, ...] = ()
    deviation: str | None = None
    expected: Dict[str, object] = field(default_factory=dict)
    channels: Tuple[str, ...] = (
        "status", "returndata", "state-projection", "eth", "logs", "call-trace"
    )


def tx(signature: str, caller: str = ACTOR, *words: int | str | bytes,
       value: int = 0, timestamp: int = 1_700_000_000) -> Tx:
    return Tx(caller, calldata(signature, *words), value=value, timestamp=timestamp)


def grant(role: int, account: str, *, timestamp: int = 1_700_000_000) -> Tx:
    return tx("grantRole(bytes32,address)", ADMIN, role, account, timestamp=timestamp)


def revoke(role: int, account: str, *, timestamp: int = 1_700_000_000) -> Tx:
    return tx("revokeRole(bytes32,address)", ADMIN, role, account, timestamp=timestamp)


class Assembler:
    def __init__(self) -> None:
        self.code = bytearray()
        self.labels: Dict[str, int] = {}
        self.fixups: List[Tuple[int, str]] = []

    def raw(self, data: bytes) -> None:
        self.code.extend(data)

    def push(self, value: int, width: int | None = None) -> None:
        raw = value.to_bytes(width or max(1, (value.bit_length() + 7) // 8), "big")
        expect(1 <= len(raw) <= 32, "invalid PUSH width")
        self.raw(bytes([0x5f + len(raw)]) + raw)

    def jumpi(self, label: str) -> None:
        self.raw(b"\x61\x00\x00\x57")
        self.fixups.append((len(self.code) - 3, label))

    def label(self, label: str) -> None:
        expect(label not in self.labels, f"duplicate label {label}")
        self.labels[label] = len(self.code)
        self.raw(b"\x5b")

    def finish(self) -> bytes:
        for at, label in self.fixups:
            expect(label in self.labels, f"missing label {label}")
            self.code[at:at + 2] = self.labels[label].to_bytes(2, "big")
        return bytes(self.code)


def dispatcher(branches: Sequence[Tuple[bytes, bytes]], fallback: bytes = b"\x5f\x5f\xfd") -> bytes:
    asm = Assembler()
    asm.raw(b"\x5f\x35\x60\xe0\x1c")  # calldata[0:4]
    for index, (sel, _body) in enumerate(branches):
        asm.raw(b"\x80\x63" + sel + b"\x14")
        asm.jumpi(f"branch-{index}")
    asm.raw(b"\x50" + fallback)
    for index, (_sel, body) in enumerate(branches):
        asm.label(f"branch-{index}")
        asm.raw(b"\x50" + body)
    return asm.finish()


def return_word(value: int) -> bytes:
    asm = Assembler()
    asm.push(value, 32)
    asm.raw(b"\x5f\x52\x60\x20\x5f\xf3")
    return asm.finish()


def recorder_body() -> bytes:
    # slot0=value, slot1=calldatasize, slot2=keccak(calldata), slot3=count,
    # slot4=caller.  The trace remains the full choreography oracle.
    return (b"\x34\x60\x00\x55" +
            b"\x36\x60\x01\x55" +
            b"\x36\x5f\x5f\x37\x36\x5f\x20\x60\x02\x55" +
            b"\x60\x03\x54\x60\x01\x01\x60\x03\x55" +
            b"\x33\x60\x04\x55\x00")


def revert_data(payload: bytes) -> bytes:
    asm = Assembler()
    for offset in range(0, len(payload), 32):
        asm.push(int.from_bytes(payload[offset:offset + 32].ljust(32, b"\0"), "big"), 32)
        asm.push(offset)
        asm.raw(b"\x52")
    asm.push(len(payload))
    asm.raw(b"\x5f\xfd")
    return asm.finish()


def mock_world(fee: int = 7, *, locator_failure: bool = False,
               fee_failure: bool = False, vault_failure: bool = False,
               router_failure: bool = False, refund_failure: bool = False) -> Dict[str, bytes]:
    failure = revert_data(bytes.fromhex("deadbeef"))
    locator = dispatcher([
        (selector("withdrawalVault()"), failure if locator_failure else return_word(int.from_bytes(address_bytes(VAULT), "big"))),
        (selector("stakingRouter()"), return_word(int.from_bytes(address_bytes(ROUTER), "big"))),
    ])
    vault = dispatcher([
        (selector("getWithdrawalRequestFee()"), failure if fee_failure else return_word(fee)),
        (selector("addWithdrawalRequests(bytes[],uint64[])"), failure if vault_failure else recorder_body()),
    ])
    router = dispatcher([
        (selector("onValidatorExitTriggered((uint256,uint256,bytes)[],uint256,uint256)"),
         failure if router_failure else recorder_body()),
    ])
    result = {LOCATOR: locator, VAULT: vault, ROUTER: router}
    if refund_failure:
        result[REJECTOR] = b"\x5f\x5f\xfd"
    return result


def build_cases() -> List[Case]:
    cases: List[Case] = []
    all_roles = [DEFAULT_ADMIN_ROLE, PAUSE_ROLE, RESUME_ROLE, ADD_ROLE, LIMIT_ROLE]
    base_accounts = [ADMIN, ACTOR, ACTOR_B, ACTOR_C, OTHER]

    def add(case: Case) -> None:
        case.observe_roles = list(dict.fromkeys(case.observe_roles + all_roles))
        case.observe_accounts = list(dict.fromkeys(case.observe_accounts + base_accounts))
        if case.family == "constructor":
            case.expected["constructorStatus"] = (
                "success" if case.name == "constructor-success" else "revert")
            if case.name != "constructor-success":
                case.expected["constructorReturndata"] = CONSTRUCTOR_RETURNDATA[case.name]
        event_tags = [tag.removeprefix("events.") for tag in case.tags
                      if tag.startswith("events.")]
        if "constructor" in event_tags:
            case.expected["eventTopics"] = [
                EVENT_TOPICS["RoleGranted"], EVENT_TOPICS["ExitRequestsLimitSet"],
            ]
        elif "RoleAdminChanged-nonemission" in event_tags:
            case.expected["eventTopics"] = []
            case.expected["eventNonemissionTopic"] = EVENT_TOPICS["RoleAdminChanged"]
        elif event_tags:
            expect(len(event_tags) == 1 and event_tags[0] in EVENT_TOPICS,
                   f"{case.name}: unsupported event semantic tags {event_tags}")
            case.expected["eventTopics"] = [EVENT_TOPICS[event_tags[0]]]
        if "trigger.fee-query" in case.tags or "trigger.fee" in case.tags:
            case.expected["feeQueryCalls"] = 1
            case.expected["feeQuerySelector"] = "0x" + selector("getWithdrawalRequestFee()").hex()
            case.expected.setdefault("feeQueryCallSuccess", "0x1")
        if "trigger.fee" in case.tags:
            case.expected["vaultCalls"] = 1
            case.expected["vaultSelector"] = "0x" + selector("addWithdrawalRequests(bytes[],uint64[])").hex()
            case.expected.setdefault("vaultCallSuccess", "0x1")
        if "trigger.router" in case.tags:
            case.expected["routerCalls"] = 1
            case.expected["routerSelector"] = "0x" + selector(
                "onValidatorExitTriggered((uint256,uint256,bytes)[],uint256,uint256)").hex()
            case.expected.setdefault("routerCallSuccess", "0x1")
        cases.append(case)

    add(Case("constructor-success", "constructor", tags=("constructor.complete-create", "events.constructor"),
             channels=("status", "state-projection", "eth", "logs")))
    for name, params in [
        ("constructor-admin-zero", {**PARAMS, "admin": ZERO}),
        ("constructor-max-too-large", {**PARAMS, "maxExitRequestsLimit": 1 << 32}),
        ("constructor-frame-too-large", {**PARAMS, "frameDurationInSec": 1 << 32}),
        ("constructor-exits-above-max", {**PARAMS, "maxExitRequestsLimit": 2, "exitsPerFrame": 3}),
        ("constructor-zero-frame", {**PARAMS, "frameDurationInSec": 0}),
    ]:
        add(Case(name, "constructor", constructor_params=params,
                 tags=("constructor.validation",), channels=("status", "returndata", "eth", "logs")))
    dirty = bytearray(constructor_suffix(PARAMS)); dirty[0] = 1
    add(Case("constructor-dirty-admin", "constructor", constructor_suffix_override=bytes(dirty),
             tags=("constructor.abi-canonical-address",), channels=("status", "returndata", "eth", "logs")))
    add(Case("constructor-nonpayable", "constructor", constructor_value=1,
             tags=("constructor.nonpayable",), channels=("status", "returndata", "eth", "logs")))

    constant_sigs = [
        "ADD_FULL_WITHDRAWAL_REQUEST_ROLE()", "DEFAULT_ADMIN_ROLE()",
        "PAUSE_INFINITELY()", "PAUSE_ROLE()", "RESUME_ROLE()",
        "TWR_LIMIT_POSITION()", "TW_EXIT_LIMIT_MANAGER_ROLE()", "VERSION()",
    ]
    for signature in constant_sigs:
        label = signature.split("(")[0].lower().replace("_", "-")
        add(Case(f"view-{label}", "selector-view", signature,
                 action=tx(signature), tags=("selector-census", "constant-view")))

    add(Case("view-supports-interface", "selector-view", "supportsInterface(bytes4)",
             action=tx("supportsInterface(bytes4)", ACTOR,
                       bytes.fromhex("5a05180f") + bytes(28)),
             tags=("selector-census", "erc165")))
    add(Case("view-role-admin", "selector-view", "getRoleAdmin(bytes32)",
             action=tx("getRoleAdmin(bytes32)", ACTOR, PAUSE_ROLE),
             tags=("selector-census", "role-admin", "events.RoleAdminChanged-nonemission")))
    add(Case("view-has-role", "selector-view", "hasRole(bytes32,address)",
             action=tx("hasRole(bytes32,address)", ACTOR, DEFAULT_ADMIN_ROLE, ADMIN),
             tags=("selector-census", "role-membership")))
    add(Case("view-is-paused-resumed", "selector-view", "isPaused()",
             action=tx("isPaused()"), tags=("selector-census", "pause.resumed")))
    add(Case("view-resume-timestamp", "selector-view", "getResumeSinceTimestamp()",
             action=tx("getResumeSinceTimestamp()"), tags=("selector-census", "pause.projection")))
    add(Case("get-limit-same-frame", "selector-view", "getExitRequestLimitFullInfo()",
             action=tx("getExitRequestLimitFullInfo()"), tags=("selector-census", "limit.same-frame")))

    add(Case("grant-role-fresh", "roles", "grantRole(bytes32,address)",
             action=grant(PAUSE_ROLE, ACTOR), tags=("selector-census", "roles.grant", "events.RoleGranted")))
    add(Case("grant-role-duplicate", "roles", "grantRole(bytes32,address)",
             history=[grant(PAUSE_ROLE, ACTOR)], action=grant(PAUSE_ROLE, ACTOR),
             tags=("roles.grant-idempotent",)))
    add(Case("revoke-role-existing", "roles", "revokeRole(bytes32,address)",
             history=[grant(PAUSE_ROLE, ACTOR)], action=revoke(PAUSE_ROLE, ACTOR),
             tags=("selector-census", "roles.revoke", "events.RoleRevoked")))
    add(Case("revoke-role-missing", "roles", "revokeRole(bytes32,address)",
             action=revoke(PAUSE_ROLE, ACTOR), tags=("roles.revoke-idempotent",)))
    add(Case("renounce-role-self", "roles", "renounceRole(bytes32,address)",
             history=[grant(PAUSE_ROLE, ACTOR)],
             action=tx("renounceRole(bytes32,address)", ACTOR, PAUSE_ROLE, ACTOR),
             tags=("selector-census", "roles.renounce", "events.RoleRevoked")))
    add(Case("renounce-role-wrong-account", "roles", "renounceRole(bytes32,address)",
             action=tx("renounceRole(bytes32,address)", ACTOR, PAUSE_ROLE, OTHER),
             tags=("deviation.TWG-D02",), deviation="TWG-D02"))
    add(Case("get-role-member", "roles", "getRoleMember(bytes32,uint256)",
             history=[grant(PAUSE_ROLE, ACTOR)],
             action=tx("getRoleMember(bytes32,uint256)", ACTOR_B, PAUSE_ROLE, 0),
             tags=("selector-census", "roles.enumeration")))
    add(Case("get-role-member-count", "roles", "getRoleMemberCount(bytes32)",
             history=[grant(PAUSE_ROLE, ACTOR)],
             action=tx("getRoleMemberCount(bytes32)", ACTOR_B, PAUSE_ROLE),
             tags=("selector-census", "roles.enumeration")))
    add(Case("get-role-member-oob", "roles", "getRoleMember(bytes32,uint256)",
             action=tx("getRoleMember(bytes32,uint256)", ACTOR, PAUSE_ROLE, 0),
             tags=("deviation.TWG-D03",), deviation="TWG-D03"))

    role_a = int.from_bytes(keccak(b"TWG_D04_ROLE_A"), "big")
    role_b = int.from_bytes(keccak(b"TWG_D04_ROLE_B"), "big")
    d04_history = [
        grant(role_a, ACTOR), grant(role_a, ACTOR_B), grant(role_a, ACTOR_C),
        grant(role_b, OTHER), grant(role_b, REFUND), revoke(role_a, ACTOR),
    ]
    add(Case("role-enumeration-cross-role-order", "roles", "getRoleMember(bytes32,uint256)",
             history=d04_history,
             action=tx("getRoleMember(bytes32,uint256)", ADMIN, role_a, 0),
             observe_roles=[role_a, role_b], observe_accounts=[REFUND],
             tags=("deviation.TWG-D04",), deviation="TWG-D04"))

    collision_role_a = int.from_bytes(keccak(b"TWG_D05_ROLE_A"), "big")
    collision_role_b = collision_role_a ^ int.from_bytes(address_bytes(ACTOR), "big") ^ \
        int.from_bytes(address_bytes(ACTOR_B), "big")
    expect((collision_role_a ^ int.from_bytes(address_bytes(ACTOR), "big")) & LOW252_MASK ==
           (collision_role_b ^ int.from_bytes(address_bytes(ACTOR_B), "big")) & LOW252_MASK,
           "D05 collision construction failed")
    add(Case("role-flat-key-collision-refusal", "roles", "hasRole(bytes32,address)",
             history=[grant(collision_role_a, ACTOR), grant(collision_role_b, ACTOR_B)],
             action=tx("hasRole(bytes32,address)", ADMIN, collision_role_b, ACTOR_B),
             observe_roles=[collision_role_a, collision_role_b],
             tags=("deviation.TWG-D05",), deviation="TWG-D05"))

    role_negatives = [
        ("role-negative-grant", "grantRole(bytes32,address)", tx("grantRole(bytes32,address)", ACTOR, PAUSE_ROLE, ACTOR_B)),
        ("role-negative-revoke", "revokeRole(bytes32,address)", tx("revokeRole(bytes32,address)", ACTOR, PAUSE_ROLE, ACTOR_B)),
        ("role-negative-pause-for", "pauseFor(uint256)", tx("pauseFor(uint256)", ACTOR, 10)),
        ("role-negative-pause-until", "pauseUntil(uint256)", tx("pauseUntil(uint256)", ACTOR, 1_700_000_010)),
        ("role-negative-resume", "resume()", tx("resume()", ACTOR)),
        ("role-negative-set-limit", "setExitRequestLimit(uint256,uint256,uint256)", tx("setExitRequestLimit(uint256,uint256,uint256)", ACTOR, 17, 3, 48)),
        ("role-negative-trigger", "triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)", Tx(ACTOR, trigger_calldata([(1, 2, bytes(range(48)))], ZERO, 4), value=7)),
    ]
    for name, signature, action in role_negatives:
        add(Case(name, "role-negative", signature, action=action,
                 code=mock_world(), observe_aux_slots={VAULT: 5, ROUTER: 5},
                 tags=("roles.negative", "deviation.TWG-D01"), deviation="TWG-D01"))

    add(Case("pause-for-finite", "pause", "pauseFor(uint256)",
             history=[grant(PAUSE_ROLE, ACTOR)], action=tx("pauseFor(uint256)", ACTOR, 10),
             tags=("selector-census", "pause.finite", "events.Paused"), expected={"resumeSince": 1_700_000_010}))
    add(Case("pause-for-sentinel", "pause", "pauseFor(uint256)",
             history=[grant(PAUSE_ROLE, ACTOR)], action=tx("pauseFor(uint256)", ACTOR, UINT256_MAX),
             tags=("pause.sentinel", "sentinel.pauseFor", "events.Paused"), expected={"resumeSince": UINT256_MAX}))
    add(Case("pause-until-finite", "pause", "pauseUntil(uint256)",
             history=[grant(PAUSE_ROLE, ACTOR)], action=tx("pauseUntil(uint256)", ACTOR, 1_700_000_010),
             tags=("selector-census", "pause.inclusive", "events.Paused"), expected={"resumeSince": 1_700_000_011}))
    add(Case("pause-until-sentinel", "pause", "pauseUntil(uint256)",
             history=[grant(PAUSE_ROLE, ACTOR)], action=tx("pauseUntil(uint256)", ACTOR, UINT256_MAX),
             tags=("pause.sentinel", "sentinel.pauseUntil", "events.Paused"), expected={"resumeSince": UINT256_MAX}))
    add(Case("pause-for-when-paused", "pause", "pauseFor(uint256)",
             history=[grant(PAUSE_ROLE, ACTOR), tx("pauseFor(uint256)", ACTOR, 10)],
             action=tx("pauseFor(uint256)", ACTOR, 5, timestamp=1_700_000_001),
             tags=("pause.polarity", "errors.ResumedExpected", "rollback"),
             expected={"actionStatus": "revert", "actionReturndata": "0x14378398",
                       "actionEventTopics": []}))
    add(Case("pause-until-when-paused", "pause", "pauseUntil(uint256)",
             history=[grant(PAUSE_ROLE, ACTOR), tx("pauseFor(uint256)", ACTOR, 10)],
             action=tx("pauseUntil(uint256)", ACTOR, 1_700_000_020,
                       timestamp=1_700_000_001),
             tags=("pause.polarity", "errors.ResumedExpected", "rollback"),
             expected={"actionStatus": "revert", "actionReturndata": "0x14378398",
                       "actionEventTopics": []}))
    add(Case("view-is-paused-paused", "pause", "isPaused()",
             history=[grant(PAUSE_ROLE, ACTOR), tx("pauseFor(uint256)", ACTOR, 10)],
             action=tx("isPaused()", timestamp=1_700_000_001), tags=("pause.paused",)))
    add(Case("resume-authorized", "pause", "resume()",
             history=[grant(PAUSE_ROLE, ACTOR), grant(RESUME_ROLE, ACTOR), tx("pauseFor(uint256)", ACTOR, 10)],
             action=tx("resume()", ACTOR, timestamp=1_700_000_001),
             tags=("selector-census", "pause.resume", "events.Resumed"), expected={"resumeSince": 1_700_000_001}))
    add(Case("pause-zero-duration", "pause", "pauseFor(uint256)",
             history=[grant(PAUSE_ROLE, ACTOR)], action=tx("pauseFor(uint256)", ACTOR, 0), tags=("pause.validation",)))
    add(Case("pause-until-past", "pause", "pauseUntil(uint256)",
             history=[grant(PAUSE_ROLE, ACTOR)], action=tx("pauseUntil(uint256)", ACTOR, 1_699_999_999), tags=("pause.validation",)))
    add(Case("resume-when-resumed", "pause", "resume()",
             history=[grant(RESUME_ROLE, ACTOR)], action=tx("resume()", ACTOR),
             tags=("pause.polarity", "errors.PausedExpected", "rollback"),
             expected={"actionStatus": "revert", "actionReturndata": "0xb047186b",
                       "actionEventTopics": []}))

    add(Case("set-limit-valid", "limit", "setExitRequestLimit(uint256,uint256,uint256)",
             history=[grant(LIMIT_ROLE, ACTOR)], action=tx("setExitRequestLimit(uint256,uint256,uint256)", ACTOR, 20, 4, 60),
             tags=("selector-census", "limit.configure", "events.ExitRequestsLimitSet")))
    for name, values in [
        ("set-limit-max-too-large", (1 << 32, 1, 48)),
        ("set-limit-frame-too-large", (17, 1, 1 << 32)),
        ("set-limit-exits-above-max", (2, 3, 48)),
        ("set-limit-zero-frame", (17, 3, 0)),
    ]:
        add(Case(name, "limit", "setExitRequestLimit(uint256,uint256,uint256)",
                 history=[grant(LIMIT_ROLE, ACTOR)],
                 action=tx("setExitRequestLimit(uint256,uint256,uint256)", ACTOR, *values),
                 tags=("limit.validation",)))

    pubkey_a = bytes(range(48))
    pubkey_b = bytes(range(48, 96))
    trigger_sig = "triggerFullWithdrawals((uint256,uint256,bytes)[],address,uint256)"
    role_history = [grant(ADD_ROLE, ACTOR)]
    trigger_common = dict(selector_signature=trigger_sig, code=mock_world(),
                          observe_aux_slots={VAULT: 5, ROUTER: 5},
                          observe_accounts=[VAULT, ROUTER, REFUND])
    add(Case("trigger-empty", "trigger", history=role_history,
             action=Tx(ACTOR, trigger_calldata([], ZERO, 4), value=1),
             tags=("selector-census", "trigger.zero-validators"), **trigger_common))
    add(Case("trigger-single-exact-fee", "trigger", history=role_history,
             action=Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a)], ZERO, 4), value=7),
             tags=("trigger.fee", "trigger.value-forward", "trigger.router", "trigger.balance-preserved"),
             expected={"vaultValue": 7, "refund": 0}, **trigger_common))
    add(Case("trigger-explicit-refund", "trigger", history=role_history,
             action=Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a)], REFUND, 4), value=10),
             tags=("trigger.fee", "trigger.value-forward", "trigger.router",
                   "trigger.refund-explicit", "trigger.balance-preserved"),
             expected={"vaultValue": 7, "routerCallSuccess": "0x1",
                       "refundTarget": REFUND, "refund": 3}, **trigger_common))
    add(Case("trigger-sender-refund", "trigger", history=role_history,
             action=Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a)], ZERO, 4), value=10),
             tags=("trigger.fee", "trigger.value-forward", "trigger.router",
                   "trigger.refund-zero-to-sender", "trigger.balance-preserved"),
             expected={"vaultValue": 7, "routerCallSuccess": "0x1",
                       "refundTarget": ACTOR, "refund": 3}, **trigger_common))
    add(Case("trigger-multiple", "trigger", history=role_history,
             action=Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a), (3, 4, pubkey_b)], REFUND, 9), value=14),
             tags=("trigger.multi", "trigger.fee", "trigger.router", "limit.consume"),
             expected={"vaultValue": 14, "routerCallSuccess": "0x1", "refund": 0},
             **trigger_common))
    add(Case("trigger-insufficient-fee", "trigger", history=role_history,
             action=Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a)], ZERO, 4), value=6),
             tags=("trigger.insufficient-fee", "rollback"), **trigger_common))
    many = [(index + 1, index + 2, pubkey_a) for index in range(18)]
    add(Case("trigger-limit-exceeded", "trigger", history=role_history,
             action=Tx(ACTOR, trigger_calldata(many, ZERO, 4), value=126),
             tags=("limit.exceeded", "rollback"), **trigger_common))
    consumed = Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a), (3, 4, pubkey_b)], ZERO, 4), value=14)
    add(Case("get-limit-refilled", "limit", "getExitRequestLimitFullInfo()",
             history=[grant(ADD_ROLE, ACTOR), consumed], code=mock_world(),
             action=tx("getExitRequestLimitFullInfo()", timestamp=1_700_000_048),
             observe_aux_slots={VAULT: 5, ROUTER: 5}, tags=("limit.consume", "limit.frame-refill")))

    add(Case("trigger-paused", "trigger", history=[grant(ADD_ROLE, ACTOR), grant(PAUSE_ROLE, ACTOR), tx("pauseFor(uint256)", ACTOR, 10)],
             action=Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a)], ZERO, 4), value=7, timestamp=1_700_000_001),
             tags=("trigger.paused", "rollback"), **trigger_common))
    add(Case("trigger-zero-value", "trigger", history=role_history,
             action=Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a)], ZERO, 4), value=0),
             tags=("trigger.zero-value", "rollback"), **trigger_common))
    for name, code, recipient, value, tags, expected in [
        ("trigger-locator-revert", mock_world(locator_failure=True), ZERO, 7,
         ("trigger.locator-revert", "rollback"), {}),
        ("trigger-fee-query-revert", mock_world(fee_failure=True), ZERO, 7,
         ("trigger.vault-fee-revert", "trigger.fee-query", "rollback"),
         {"feeQueryCallSuccess": "0x0"}),
        ("trigger-vault-revert", mock_world(vault_failure=True), ZERO, 7,
         ("trigger.vault-revert", "trigger.fee", "trigger.value-forward", "rollback"),
         {"feeQueryCallSuccess": "0x1", "vaultCallSuccess": "0x0", "vaultValue": 7}),
        ("trigger-router-revert", mock_world(router_failure=True), ZERO, 7,
         ("trigger.router-revert", "trigger.fee", "trigger.value-forward",
          "trigger.router", "rollback"),
         {"feeQueryCallSuccess": "0x1", "vaultCallSuccess": "0x1",
          "vaultValue": 7, "routerCallSuccess": "0x0"}),
        ("trigger-refund-revert", mock_world(refund_failure=True), REJECTOR, 10,
         ("trigger.refund-revert", "trigger.fee", "trigger.value-forward",
          "trigger.router", "trigger.balance-preserved", "rollback"),
         {"feeQueryCallSuccess": "0x1", "vaultCallSuccess": "0x1",
          "vaultValue": 7, "routerCallSuccess": "0x1",
          "refundTarget": REJECTOR, "refund": 3}),
    ]:
        add(Case(name, "trigger", trigger_sig, history=role_history,
                 action=Tx(ACTOR, trigger_calldata([(1, 2, pubkey_a)], recipient, 4), value=value),
                 code=code, observe_aux_slots={VAULT: 5, ROUTER: 5},
                 observe_accounts=[VAULT, ROUTER, recipient], tags=tags, expected=expected))

    names = [case.name for case in cases]
    expect(len(names) == len(set(names)), "duplicate case name")
    return cases


def parse_artifacts(text: str) -> Dict[str, object]:
    result: Dict[str, object] = {"offsets": {}, "projection": {}}
    byte_labels = {"creation-template", "primary-create", "primary-runtime",
                   "independent-create", "independent-runtime"}
    for line in text.splitlines():
        parts = line.split()
        if not parts:
            continue
        label = parts[0]
        if label in byte_labels:
            expect(len(parts) == 3, f"malformed evaluator row {label}")
            raw = bytes.fromhex(parts[2])
            expect(len(raw) == int(parts[1]), f"evaluator length mismatch for {label}")
            result[label] = raw
        elif label == "selectors":
            values = parts[2].split(",") if int(parts[1]) else []
            expect(len(values) == int(parts[1]), "evaluator selector count mismatch")
            result[label] = ["0x" + value[-8:].lower() for value in values]
        elif label == "offsets-locator":
            values = parts[2].split(",") if int(parts[1]) else []
            result["offsets"] = {"locator": [int(value) for value in values]}
        elif label in {"offset-metadata-valid", "patch-controls-valid"}:
            result[label] = parts[1] == "true"
        elif label == "constructor-persistent-sites":
            rows = [] if parts[2] == "-" else parts[2].split(",")
            expect(len(rows) == int(parts[1]), "constructor inventory length mismatch")
            result[label] = rows
        elif label == "constructor-external-sites":
            result[label] = [] if parts[2] == "-" else parts[2].split(",")
            expect(len(result[label]) == int(parts[1]), "constructor external inventory mismatch")
        elif label in {"projection-regions", "projection-region-words", "projection-slots"}:
            rows = [entry.split("|") for entry in parts[2].split(",")]
            expect(len(rows) == int(parts[1]) and all(len(row) == 2 for row in rows),
                   f"malformed {label}")
            result["projection"][label] = dict(rows)
        elif label == "projection-formula":
            result["projection"]["formula"] = parts[1]
        elif label in {"constructor-arguments", "constructor-events"}:
            result[label] = parts[1].split(",")
        elif label == "limits":
            result[label] = tuple(map(int, parts[1:]))
        elif label == "sizes":
            result[label] = tuple(map(int, parts[1:]))
    required = byte_labels | {"selectors", "offset-metadata-valid", "patch-controls-valid",
                              "constructor-persistent-sites", "constructor-external-sites",
                              "constructor-arguments", "constructor-events", "limits", "sizes"}
    expect(not (required - result.keys()), f"Lean evaluator omitted {sorted(required - result.keys())}")
    expect(result["offset-metadata-valid"] is True and result["patch-controls-valid"] is True,
           "Lean evaluator patch controls are not live")
    expect(len(result["offsets"]["locator"]) >= 1, "locator patch inventory is empty")
    expect(len(result["constructor-persistent-sites"]) == 11 and not result["constructor-external-sites"],
           "constructor source-site inventory drifted")
    expect(result["constructor-arguments"] == ["admin", "locator", "max-exit-requests", "exits-per-frame", "frame-duration"],
           "constructor argument inventory drifted")
    expect(result["constructor-events"] == ["RoleGranted", "ExitRequestsLimitSet"],
           "constructor event inventory drifted")
    return result


def validate_identities(lock: Mapping, census: Mapping, artifacts: Mapping) -> int:
    checks = 0
    expect(subprocess.run(
        ["git", "merge-base", "--is-ancestor", BLANC_ARTIFACT_COMMIT, BLANC_PROOF_COMMIT],
        cwd=REPO, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0,
        "pinned Blanc artifact program is not an ancestor of the proof certificate")
    expect(subprocess.run(
        ["git", "merge-base", "--is-ancestor", BLANC_PROOF_COMMIT, "HEAD"],
        cwd=REPO, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0,
        "pinned Blanc proof certificate is not an ancestor of the candidate")
    checks += 1
    functions = census["selectors"]
    expected_selectors = [row["selector"] for row in functions]
    expect(len(artifacts["selectors"]) == len(expected_selectors) and
           set(artifacts["selectors"]) == set(expected_selectors),
           "Lean selector inventory differs from the exact census")
    checks += 1
    template = artifacts["creation-template"]
    primary_expected = template + constructor_suffix({
        **PARAMS, "maxExitRequestsLimit": 1000, "exitsPerFrame": 10,
        "frameDurationInSec": 3600,
    })
    expect(artifacts["primary-create"] == primary_expected,
           "Lean primary full CREATE is not template plus exact suffix")
    checks += 1
    expect(artifacts["independent-create"] ==
           template + constructor_suffix(INDEPENDENT_PARAMS),
           "Lean independent full CREATE is not template plus exact suffix")
    checks += 1
    expect(artifacts["primary-runtime"] == patch_blanc_runtime(artifacts, LOCATOR),
           "Lean primary runtime is not the neutral-template locator patch")
    checks += 1
    expect(artifacts["independent-runtime"] ==
           patch_blanc_runtime(artifacts, str(INDEPENDENT_PARAMS["lidoLocator"])),
           "Lean independent runtime is not the neutral-template locator patch")
    checks += 1
    runtime_differences = {
        index for index, (primary, independent) in enumerate(zip(
            artifacts["primary-runtime"], artifacts["independent-runtime"]))
        if primary != independent
    }
    declared_differences = {
        index for offset in artifacts["offsets"]["locator"]
        for index in range(offset, offset + 32)
        if address_word(LOCATOR)[index - offset] !=
        address_word(str(INDEPENDENT_PARAMS["lidoLocator"]))[index - offset]
    }
    expect(runtime_differences == declared_differences,
           "runtime worlds differ outside their declared locator words")
    checks += 1
    world = next(item for item in lock["artifacts"]["worlds"] if item["name"] == REFERENCE_WORLD)
    sol_template = bytes.fromhex(lock["artifacts"]["creationTemplate"]["hex"].removeprefix("0x"))
    sol_create = sol_template + constructor_suffix(PARAMS)
    expect(sol_create == bytes.fromhex(world["fullCreateInput"]["hex"].removeprefix("0x")),
           "reference differential-world full CREATE derivation drifted")
    checks += 1
    expect(patch_solidity_runtime(lock, LOCATOR) ==
           bytes.fromhex(world["returnedRuntime"]["hex"].removeprefix("0x")),
           "reference differential-world runtime derivation drifted")
    checks += 1
    expect(len(template) + 160 <= 49_152 and len(artifacts["primary-runtime"]) <= 24_576,
           "Blanc artifacts exceed EIP limits")
    checks += 1
    return checks


def patch_blanc_runtime(artifacts: Mapping, locator: str) -> bytes:
    runtime_length = int(artifacts["sizes"][0])
    creation_template = artifacts["creation-template"]
    expect(0 < runtime_length <= len(creation_template),
           "invalid neutral runtime-template length")
    code = bytearray(creation_template[-runtime_length:])
    word = address_word(locator)
    for offset in artifacts["offsets"]["locator"]:
        code[offset:offset + 32] = word
    return bytes(code)


def patch_solidity_runtime(lock: Mapping, locator: str) -> bytes:
    code = bytearray(bytes.fromhex(lock["artifacts"]["runtimeTemplate"]["hex"].removeprefix("0x")))
    immutable_names = lock["artifacts"]["immutableNames"]
    for ast_id, spans in lock["artifacts"]["immutableReferences"].items():
        expect(immutable_names[ast_id] == "LOCATOR", "unknown Solidity immutable")
        for span in spans:
            expect(span["length"] == 32, "Solidity locator immutable is not one word")
            code[span["start"]:span["start"] + 32] = address_word(locator)
    return bytes(code)


def read_storage(state, address: str, key: int) -> int:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_storage
    from ethereum_types.bytes import Bytes32
    return int(get_storage(state, Address(address_bytes(address)), Bytes32(h256(key))))


def sol_map(key_word: bytes, base: int) -> int:
    return int.from_bytes(keccak(key_word + h256(base)), "big")


def tagged(region: int, payload: int = 0) -> int:
    return (region << REGION_SHIFT) | (payload & LOW252_MASK)


def role_payload(role: int, account: str) -> int:
    return (role ^ int.from_bytes(address_bytes(account), "big")) & LOW252_MASK


def project_state(case: Case, state, side: str) -> Mapping[str, object]:
    roles_position = int.from_bytes(keccak(b"openzeppelin.AccessControl._roles"), "big")
    role_members_position = int.from_bytes(
        keccak(b"openzeppelin.AccessControlEnumerable._roleMembers"), "big")
    resume_position = int.from_bytes(
        keccak(b"lido.PausableUntil.resumeSinceTimestamp"), "big")
    limit_position = int.from_bytes(
        keccak(b"lido.TriggerableWithdrawalsGateway.maxExitRequestLimit"), "big")

    roles = sorted(set(case.observe_roles), key=lambda value: h256(value))
    accounts = sorted(set(case.observe_accounts), key=canonical_address)
    if side == "solidity":
        resume_since = read_storage(state, GATEWAY, resume_position)
        packed = read_storage(state, GATEWAY, limit_position)
        limit = {
            "maximum": hex(packed & 0xffffffff),
            "previous": hex((packed >> 32) & 0xffffffff),
            "timestamp": hex((packed >> 64) & 0xffffffff),
            "frameDuration": hex((packed >> 96) & 0xffffffff),
            "exitsPerFrame": hex((packed >> 128) & 0xffffffff),
        }

        def role_projection(role: int) -> Mapping[str, object]:
            role_slot = sol_map(h256(role), roles_position)
            enum_slot = sol_map(h256(role), role_members_position)
            length = read_storage(state, GATEWAY, enum_slot)
            expect(length <= 64, f"refusing Solidity role array length {length}")
            array_base = int.from_bytes(keccak(h256(enum_slot)), "big")
            members = [canonical_address("0x" + h256(
                read_storage(state, GATEWAY, (array_base + index) & UINT256_MAX)
            )[-20:].hex()) for index in range(length)]
            membership = {}
            for account in accounts:
                member_slot = sol_map(address_word(account), role_slot)
                membership[canonical_address(account)] = bool(read_storage(state, GATEWAY, member_slot))
            return {"adminRole": role_hex(read_storage(state, GATEWAY, (role_slot + 1) & UINT256_MAX)),
                    "members": members, "membership": membership}
    else:
        resume_since = read_storage(state, GATEWAY, tagged(1, 0))
        limit = {
            "maximum": hex(read_storage(state, GATEWAY, tagged(1, 1))),
            "previous": hex(read_storage(state, GATEWAY, tagged(1, 2))),
            "timestamp": hex(read_storage(state, GATEWAY, tagged(1, 3))),
            "frameDuration": hex(read_storage(state, GATEWAY, tagged(1, 4))),
            "exitsPerFrame": hex(read_storage(state, GATEWAY, tagged(1, 5))),
        }
        record_length = read_storage(state, GATEWAY, tagged(1, 6))
        expect(record_length <= 64,
               f"{case.name}/{side}: refusing Blanc role record length {record_length}")

        def role_projection(role: int) -> Mapping[str, object]:
            members: List[str] = []
            for index in range(record_length):
                stored_role = read_storage(state, GATEWAY, tagged(5, index))
                account_value = read_storage(state, GATEWAY, tagged(6, index))
                if stored_role == role:
                    members.append(canonical_address("0x" + h256(account_value)[-20:].hex()))
            membership = {}
            for account in accounts:
                payload = role_payload(role, account)
                membership[canonical_address(account)] = (
                    read_storage(state, GATEWAY, tagged(4, payload)) != 0 and
                    read_storage(state, GATEWAY, tagged(2, payload)) == role and
                    read_storage(state, GATEWAY, tagged(3, payload)) ==
                    int.from_bytes(address_bytes(account), "big"))
            return {"adminRole": role_hex(DEFAULT_ADMIN_ROLE),
                    "members": members, "membership": membership}

    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import get_account
    addresses = {GATEWAY, CREATE_CALLER, *case.observe_accounts, *case.code.keys(),
                 *(item.caller for item in case.history)}
    if case.action:
        addresses.add(case.action.caller)
    eth = {canonical_address(address): hex(int(get_account(
        state, Address(address_bytes(address))).balance))
        for address in sorted(addresses, key=canonical_address)}
    auxiliary = {
        canonical_address(address): [hex(read_storage(state, address, slot))
                                     for slot in range(count)]
        for address, count in sorted(case.observe_aux_slots.items(),
                                     key=lambda item: canonical_address(item[0]))
    }
    return {
        "logicalState": {
            "resumeSince": hex(resume_since), "limit": limit,
            "roles": {role_hex(role): role_projection(role) for role in roles},
        },
        "eth": eth,
        "auxiliaryState": auxiliary,
    }


def side_artifacts(side: str, params: Mapping[str, object], lock: Mapping,
                   artifacts: Mapping) -> Tuple[bytes, bytes]:
    if side == "solidity":
        template = bytes.fromhex(lock["artifacts"]["creationTemplate"]["hex"].removeprefix("0x"))
        runtime = patch_solidity_runtime(lock, str(params["lidoLocator"]))
    else:
        template = artifacts["creation-template"]
        runtime = patch_blanc_runtime(artifacts, str(params["lidoLocator"]))
    return template, runtime


def normalize_output(output, trace: Sequence[Mapping], gas: int) -> Mapping[str, object]:
    return {
        "status": eels.outcome(output),
        "returndata": "0x" + bytes(output.return_data).hex(),
        "logs": eels.normalized_logs(output.logs),
        "callTrace": list(trace),
        "gasUsed": gas,
    }


def run_side(case: Case, side: str, lock: Mapping, artifacts: Mapping) -> Mapping[str, object]:
    from ethereum.prague.fork_types import Address
    from ethereum.prague.state import State, get_account_optional

    state = State()
    template, expected_runtime = side_artifacts(side, case.constructor_params, lock, artifacts)
    suffix = case.constructor_suffix_override
    if suffix is None:
        suffix = constructor_suffix(case.constructor_params)
    create_input = template + suffix + case.constructor_trailing
    created, installed, create_gas = eels.execute_create(
        state, GATEWAY, create_input, case.constructor_value,
        address_bytes=address_bytes, coinbase=COINBASE, create_caller=CREATE_CALLER,
        gas=DEFAULT_GAS_LIMIT)
    created_status = eels.outcome(created)
    account_exists = get_account_optional(state, Address(address_bytes(GATEWAY))) is not None
    if created_status == "success":
        expect(installed == expected_runtime and bytes(created.return_data) == expected_runtime,
               f"{case.name}/{side}: CREATE did not install/return owned runtime")
        expect(len(installed) <= 24_576 and len(create_input) <= 49_152,
               f"{case.name}/{side}: artifact exceeds EIP limit")
    else:
        expect(not account_exists, f"{case.name}/{side}: failed CREATE left an account")

    if case.family == "constructor":
        projected = project_state(case, state, side) if created_status == "success" else {
            "logicalState": {}, "eth": project_state(case, state, side)["eth"],
            "auxiliaryState": {},
        }
        return {
            "status": [created_status],
            "returndata": ["0x" + bytes(created.return_data).hex()],
            "logs": [eels.normalized_logs(created.logs)], "callTrace": [[]],
            "gasUsed": [create_gas], **projected,
            "boundaries": [{"label": "constructor", "gasUsed": create_gas,
                            "status": created_status}],
            "artifact": {"createInputSha256": sha256(create_input),
                         "runtimeSha256": sha256(installed) if installed else None,
                         "createInputBytes": len(create_input),
                         "runtimeBytes": len(installed)},
        }

    expect(created_status == "success", f"{case.name}/{side}: seed CREATE failed")
    eels.install_code(state, case.code, address_bytes=address_bytes)
    rows: List[Mapping[str, object]] = []
    boundaries: List[Mapping[str, object]] = [{
        "label": "constructor", "gasUsed": create_gas, "status": created_status,
    }]
    for index, message in enumerate([*case.history, *([case.action] if case.action else [])]):
        output, trace, gas, _writes, _resource_ops = eels.execute_tx(
            state, message, address_bytes=address_bytes, coinbase=COINBASE,
            default_origin=CREATE_CALLER, fail=die)
        rows.append(normalize_output(output, trace, gas))
        label = "action" if index == len(case.history) else f"history-{index}"
        boundaries.append({"label": label, "gasUsed": gas,
                           "status": eels.outcome(output)})
    projected = project_state(case, state, side)
    return {
        "status": [row["status"] for row in rows],
        "returndata": [row["returndata"] for row in rows],
        "logs": [row["logs"] for row in rows],
        "callTrace": [row["callTrace"] for row in rows],
        "gasUsed": [row["gasUsed"] for row in rows],
        **projected, "boundaries": boundaries,
        "artifact": {"createInputSha256": sha256(create_input),
                     "runtimeSha256": sha256(installed),
                     "createInputBytes": len(create_input),
                     "runtimeBytes": len(installed)},
    }


def compared_fields(case: Case) -> List[str]:
    fields: List[str] = []
    for channel in case.channels:
        fields.extend(CHANNEL_FIELDS[channel])
    return list(dict.fromkeys(fields))


def compare(case: Case, solidity: Mapping, blanc: Mapping) -> List[str]:
    return [field for field in compared_fields(case) if solidity[field] != blanc[field]]


def assert_case(case: Case, solidity: Mapping, blanc: Mapping) -> None:
    mismatch = tuple(compare(case, solidity, blanc))
    expected = DEVIATION_FIELDS.get(case.deviation, ())
    expect(set(mismatch) == set(expected),
           f"{case.name}: mismatch fields {mismatch}, expected {expected}")
    if case.deviation:
        expect(mismatch, f"{case.name}: declared deviation does not discriminate")
    action_index = -1
    for side, result in (("solidity", solidity), ("blanc", blanc)):
        traces = result["callTrace"][action_index]
        if case.family == "constructor":
            expect(result["status"][action_index] == case.expected["constructorStatus"],
                   f"{case.name}/{side}: constructor outcome differs")
            if "constructorReturndata" in case.expected:
                expect(result["returndata"][action_index] ==
                       case.expected["constructorReturndata"],
                       f"{case.name}/{side}: constructor error payload differs")
                expect(not result["logs"][action_index],
                       f"{case.name}/{side}: failed constructor retained logs")
        if case.expected.get("resumeSince") is not None:
            expect(result["logicalState"]["resumeSince"] == hex(int(case.expected["resumeSince"])),
                   f"{case.name}/{side}: pause projection differs")
        if any(tag.startswith("roles.negative") for tag in case.tags):
            expect(result["status"][action_index] == "revert",
                   f"{case.name}/{side}: role negative did not revert")
        if "trigger.balance-preserved" in case.tags:
            gateway_balance = result["eth"][canonical_address(GATEWAY)]
            expect(gateway_balance == "0x0", f"{case.name}/{side}: ETH balance not preserved")
        if "vaultValue" in case.expected:
            vault_calls = [row for row in traces if row["target"] == canonical_address(VAULT)
                           and row["input"].startswith("0x" + selector("addWithdrawalRequests(bytes[],uint64[])").hex())]
            expect(len(vault_calls) == 1 and int(vault_calls[0]["value"], 16) == case.expected["vaultValue"],
                   f"{case.name}/{side}: vault value-forwarding evidence differs")
        if "feeQueryCalls" in case.expected:
            fee_calls = [row for row in traces
                         if row["target"] == canonical_address(VAULT)
                         and row["input"] == case.expected["feeQuerySelector"]]
            expect(len(fee_calls) == case.expected["feeQueryCalls"]
                   and fee_calls[0]["opcode"] == "STATICCALL"
                   and fee_calls[0].get("success") == case.expected["feeQueryCallSuccess"],
                   f"{case.name}/{side}: fee-query call evidence differs")
        if "vaultCalls" in case.expected:
            vault_calls = [row for row in traces
                           if row["target"] == canonical_address(VAULT)
                           and row["input"].startswith(case.expected["vaultSelector"])]
            expect(len(vault_calls) == case.expected["vaultCalls"]
                   and vault_calls[0].get("success") == case.expected["vaultCallSuccess"],
                   f"{case.name}/{side}: addWithdrawalRequests call evidence differs")
        if "routerCalls" in case.expected:
            router_calls = [row for row in traces
                            if row["target"] == canonical_address(ROUTER)
                            and row["input"].startswith(case.expected["routerSelector"])]
            expect(len(router_calls) == case.expected["routerCalls"]
                   and router_calls[0].get("success") == case.expected["routerCallSuccess"],
                   f"{case.name}/{side}: router notification call evidence differs")
        if case.expected.get("refund", 0):
            refund_calls = [row for row in traces
                            if row["target"] == canonical_address(str(case.expected["refundTarget"]))
                            and int(row["value"], 16) == case.expected["refund"]]
            expect(len(refund_calls) == 1, f"{case.name}/{side}: refund arm not observed")
        if "eventTopics" in case.expected:
            actual_topics = [row["topics"][0] for row in result["logs"][action_index]]
            expect(actual_topics == case.expected["eventTopics"],
                   f"{case.name}/{side}: exact event topics/order differs: {actual_topics}")
        if "actionStatus" in case.expected:
            expect(result["status"][action_index] == case.expected["actionStatus"]
                   and result["returndata"][action_index] == case.expected["actionReturndata"]
                   and [row["topics"][0] for row in result["logs"][action_index]] ==
                   case.expected["actionEventTopics"],
                   f"{case.name}/{side}: exact action failure semantic differs")


def evidence(result: Mapping) -> Mapping[str, object]:
    return {
        "status": result["status"],
        "returndataSha256": digest(result["returndata"]),
        "logicalStateSha256": digest(result["logicalState"]),
        "auxiliaryStateSha256": digest(result["auxiliaryState"]),
        "ethSha256": digest(result["eth"]),
        "logsSha256": digest(result["logs"]),
        "callTraceSha256": digest(result["callTrace"]),
        "gasUsed": result["gasUsed"],
    }


def projection_schema(artifacts: Mapping) -> Mapping[str, object]:
    return {
        "schema": 1,
        "boundary": ["resumeSince", "exit-limit-five-field-record",
                     "per-role-admin-membership-count-and-ordered-members",
                     "selected-account-ETH", "selected-mock-storage"],
        "solidity": {
            "pause": "keccak256(lido.PausableUntil.resumeSinceTimestamp)",
            "limit": "packed uint32 fields at keccak256(lido.TriggerableWithdrawalsGateway.maxExitRequestLimit)",
            "roles": "OpenZeppelin unstructured role mapping and per-role EnumerableSet",
        },
        "blanc": {
            "formula": artifacts["projection"].get("formula"),
            "regions": artifacts["projection"].get("projection-regions"),
            "slots": artifacts["projection"].get("projection-slots"),
            "roles": "full-identity lookup records plus filtered global enumeration",
        },
        "nonclaim": "raw slots, storage roots, bytecode, and enumeration order at TWG-D04 are not equated",
    }


def resource_rows(cases: Sequence[Case], results: Mapping[str, Tuple[Mapping, Mapping]]) -> List[Mapping[str, object]]:
    rows: List[Mapping[str, object]] = []
    ordinal = 0
    for case in cases:
        solidity, blanc = results[case.name]
        expect(len(solidity["boundaries"]) == len(blanc["boundaries"]),
               f"{case.name}: resource boundary cardinality differs")
        for index, (sol, bla) in enumerate(zip(solidity["boundaries"], blanc["boundaries"])):
            expect(sol["label"] == bla["label"], f"{case.name}: boundary label differs")
            rows.append({
                "ordinal": ordinal,
                "coordinate": f"{case.name}#{index}:{sol['label']}",
                "case": case.name, "label": sol["label"],
                "referenceStatus": sol["status"], "blancStatus": bla["status"],
                "referenceGas": sol["gasUsed"], "blancGas": bla["gasUsed"],
                "delta": bla["gasUsed"] - sol["gasUsed"],
            })
            ordinal += 1
    return rows


def named_gas_rows(resources: Sequence[Mapping]) -> List[Mapping[str, object]]:
    by_case: Dict[str, List[Mapping]] = {}
    for row in resources:
        by_case.setdefault(str(row["case"]), []).append(row)
    result = []
    for key, path, case_name in GAS_CASES:
        candidates = by_case[case_name]
        chosen = candidates[0] if case_name == "constructor-success" else candidates[-1]
        result.append({
            "gasKey": key, "path": path,
            "coordinate": chosen["coordinate"],
            "reference": chosen["referenceGas"], "blanc": chosen["blancGas"],
            "delta": chosen["delta"],
        })
    final_actions = {
        str(case): rows[-1] for case, rows in by_case.items()
        if case != "constructor-success" and rows[-1]["label"] == "action"
    }
    expect(len(final_actions) == 63,
           "public final-action inventory must contain exactly the 63 non-constructor rows")
    expected_positive = {
        str(row["coordinate"]) for row in final_actions.values() if row["delta"] > 0
    }
    constructor = by_case["constructor-success"][0]
    expect(constructor["label"] == "constructor" and constructor["delta"] > 0,
           "successful constructor positive-cost boundary differs")
    expected_positive.add(str(constructor["coordinate"]))
    actual_positive = {str(row["coordinate"]) for row in result if row["delta"] > 0}
    expect(actual_positive == expected_positive and len(actual_positive) == 48,
           "named gas rows do not cover every positive public final action plus constructor")
    actual_nonpositive = {
        str(row["coordinate"]).split("#", 1)[0]
        for row in result if row["delta"] <= 0
    }
    expect(actual_nonpositive == RETAINED_NONPOSITIVE_GAS_CASES,
           "named gas rows do not retain the exact three negative review controls")
    return result


def gas_cost_disposition(row: Mapping[str, object]) -> Tuple[str, str]:
    case = str(row["coordinate"]).split("#", 1)[0]
    if case == "constructor-success":
        return (
            "Accepted deployment cost for explicit constructor validation, tagged role/limit "
            "initialization, and runtime code deposit; no deployment-gas improvement is claimed.",
            "deployment initialization and code-deposit boundary",
        )
    if case.startswith("trigger-"):
        return (
            "Accepted trigger-path cost for explicit fee, vault, router, refund, and rollback "
            "choreography; the corpus pins effects and no aggregate gas advantage is claimed.",
            "trigger dependency/value/rollback boundary",
        )
    if case.startswith("set-limit-") or case.startswith("get-limit-"):
        return (
            "Accepted exit-limit cost for explicit five-field projection, validation, checked "
            "consumption, or whole-frame refill; the measured behavior is independently pinned.",
            "exit-limit projection and validation boundary",
        )
    if case.startswith("pause-") or case.startswith("resume-"):
        return (
            "Accepted pause-control cost for explicit authorization, sentinel/error-polarity "
            "checks, and tagged-state update or rollback; no gas improvement is claimed.",
            "pause/resume authorization and tagged-state boundary",
        )
    if (case.startswith("grant-role") or case.startswith("revoke-role") or
            case.startswith("renounce-role") or case.startswith("get-role-member") or
            case.startswith("role-")):
        return (
            "Accepted role-state cost for full-identity collision checks and global enumeration "
            "maintenance or scanning; TWG-D02–D05 separately delimit observable differences.",
            "full-identity role lookup/enumeration boundary",
        )
    return (
        "Accepted read-path cost of Blanc's explicit dispatcher and proof-local tagged "
        "representation; exact output semantics are pinned and no gas improvement is claimed.",
        "constant, interface, role, or pause-state read boundary",
    )


def compatibility_contract() -> Mapping[str, object]:
    raw = subprocess.check_output(
        [sys.executable, str(COMPATIBILITY_TOOL), "schema"], cwd=REPO)
    value = json.loads(raw)
    expect(set(value) == {"documentFill"}, "compatibility schema command changed shape")
    contract = value["documentFill"]
    current_templates = contract["templates"]
    if current_templates != PLACEHOLDER_TEMPLATE_DIGESTS:
        compatibility = (REPO / "LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_COMPATIBILITY.md").read_text()
        deviations = (REPO / "LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_DEVIATIONS.md").read_text()
        expect("{{MACHINE:" not in compatibility + deviations,
               "claim templates drifted before their one-way document fill")
        contract["templates"] = dict(PLACEHOLDER_TEMPLATE_DIGESTS)
    return contract


def build_document_fill(contract: Mapping, cases: Sequence[Case], resources: Sequence[Mapping],
                        artifacts: Mapping, lock: Mapping, census: Mapping,
                        projection: Mapping) -> Mapping[str, object]:
    fill = copy.deepcopy(contract)
    named = named_gas_rows(resources)
    positives = []
    for row in named:
        if row["delta"] > 0:
            defense, review_group = gas_cost_disposition(row)
            positives.append({
                "id": f"TWG-G{len(positives) + 1:02d}", "gasKey": row["gasKey"],
                "defense": defense,
                "evidence": f"manifest resource coordinate {row['coordinate']}; {review_group}",
            })
    template = artifacts["creation-template"]
    full = template + constructor_suffix(PARAMS)
    runtime = patch_blanc_runtime(artifacts, LOCATOR)
    fill["evidence"] = {
        "artifactProgramCommit": BLANC_ARTIFACT_COMMIT,
        "proofCertificateCommit": BLANC_PROOF_COMMIT,
        "artifacts": {
            "creationTemplate": {"byteLength": len(template), "sha256": sha256(template)},
            "fullCreateInput": {"byteLength": len(full), "sha256": sha256(full)},
            "runtime": {"byteLength": len(runtime), "sha256": sha256(runtime)},
        },
        "counts": {"cases": len(cases), "resourceBoundaries": len(resources)},
        "gas": {"boundaryDefinition": BOUNDARY_DEFINITION,
                "rows": named, "positiveDeviations": positives},
        "summaries": {
            "B2_CALLDATA_SCOPE_SUMMARY": "canonical ABI endpoint rows plus named dirty-address constructor rejection; nested malformed dynamic ABI, empty/unknown/short dispatch, trailing calldata, and recognized-selector nonpayability are untested and excluded",
            "B2_CODE_SIZE_HEADROOM_SUMMARY": f"runtime {len(runtime)} bytes ({24576-len(runtime)} EIP-170 headroom); full CREATE {len(full)} bytes ({49152-len(full)} EIP-3860 headroom)",
            "B2_CONSTRUCTOR_COVERAGE_SUMMARY": "complete CREATE success plus zero admin, dirty admin, value, and four exit-limit validation failures",
            "B2_COVERAGE_SUMMARY": f"{len(cases)} named rows cover 24/24 selectors, constructor, five reachable emitted event kinds plus RoleAdminChanged non-emission, pause sentinel/error-polarity arms, roles, configured-limit consumption/exceeded/whole-frame refill, and trigger mocks; zero/unlimited and partial-frame limit behavior plus the excluded dispatch/calldata arms are untested",
            "B2_D01_ROW_SET": ", ".join(case.name for case in cases if case.deviation == "TWG-D01"),
            "B2_D01_SIZE_ATTRIBUTION": "seven exact unauthorized-role returndata rows; status, rollback, state, ETH, logs, and calls agree",
            "B2_D02_RESOURCE_ATTRIBUTION": "wrong-account renounce action gas is pinned in the complete resource vector",
            "B2_D02_ROW_SET": ", ".join(case.name for case in cases if case.deviation == "TWG-D02"),
            "B2_D03_RESOURCE_ATTRIBUTION": "out-of-bounds getRoleMember action gas and exact two payload digests are pinned",
            "B2_D03_ROW_SET": ", ".join(case.name for case in cases if case.deviation == "TWG-D03"),
            "B2_D04_EXPECTED_ORDERS": "reference role-A order [ACTOR_C, ACTOR_B]; Blanc filtered global order [ACTOR_B, ACTOR_C]",
            "B2_D04_ROW_SET": ", ".join(case.name for case in cases if case.deviation == "TWG-D04"),
            "B2_D05_PROJECTION_SHA256": digest(projection),
            "B2_D05_RESOURCE_ATTRIBUTION": "colliding second grant and subsequent hasRole boundaries are pinned",
            "B2_D05_ROW_SET": ", ".join(case.name for case in cases if case.deviation == "TWG-D05"),
            "B2_DIFFERENTIAL_VERDICT": "PASS",
            "B2_PER_SELECTOR_RESOURCE_COVERAGE_SUMMARY": "24/24 census selectors each own at least one direct action boundary",
            "B2_PROJECTION_SCHEMA_SHA256": digest(projection),
        },
    }
    return fill


def build_manifest(cases: Sequence[Case], results: Mapping[str, Tuple[Mapping, Mapping]],
                   resources: Sequence[Mapping], lock: Mapping, census: Mapping,
                   artifacts: Mapping, identity_checks: int) -> Mapping[str, object]:
    projection = projection_schema(artifacts)
    selector_rows: Dict[str, List[str]] = {row["signature"]: [] for row in census["selectors"]}
    rows = []
    for ordinal, case in enumerate(cases):
        solidity, blanc = results[case.name]
        if case.selector_signature:
            selector_rows[case.selector_signature].append(case.name)
        rows.append({
            "ordinal": ordinal, "name": case.name, "family": case.family,
            "selector": case.selector_signature,
            "tags": list(case.tags), "channels": list(case.channels),
            "deviation": case.deviation,
            "expectedMismatchFields": list(DEVIATION_FIELDS.get(case.deviation, ())),
            "semantic": {"assertions": list(case.tags), "expected": case.expected},
            "reference": evidence(solidity), "blanc": evidence(blanc),
            "semanticDigest": digest({
                "assertions": case.tags, "expected": case.expected,
                "reference": evidence(solidity), "blanc": evidence(blanc),
            }),
        })
    expect(all(selector_rows.values()),
           "manifest has a census selector without an action row")
    deviation_rows = {
        deviation: [case.name for case in cases if case.deviation == deviation]
        for deviation in DEVIATION_FIELDS
    }
    all_tags = sorted({tag for case in cases for tag in case.tags})
    manifest: Dict[str, object] = {
        "schema": 1,
        "contract": "TriggerableWithdrawalsGateway",
        "oracle": {
            "engine": "ethereum/execution-specs", "fork": "Prague",
            "eelsCommit": EELS_PIN, "jauneCommit": JAUNE_PIN,
            "referenceLockSha256": sha256(LOCK_PATH.read_bytes()),
            "censusSha256": sha256(CENSUS_PATH.read_bytes()),
            "referenceWorld": REFERENCE_WORLD,
            "deployment": "fresh state; each side executes its complete CREATE input",
        },
        "artifacts": {
            "reference": {
                "creationTemplate": {"byteLength": lock["artifacts"]["creationTemplate"]["byteLength"],
                                     "sha256": lock["artifacts"]["creationTemplate"]["sha256"]},
                "runtimeTemplate": {"byteLength": lock["artifacts"]["runtimeTemplate"]["byteLength"],
                                    "sha256": lock["artifacts"]["runtimeTemplate"]["sha256"]},
                "fullCreateInput": {"byteLength": results["constructor-success"][0]["artifact"]["createInputBytes"],
                                    "sha256": results["constructor-success"][0]["artifact"]["createInputSha256"]},
                "runtime": {"byteLength": results["constructor-success"][0]["artifact"]["runtimeBytes"],
                            "sha256": results["constructor-success"][0]["artifact"]["runtimeSha256"]},
            },
            "blanc": {
                "creationTemplate": {"byteLength": len(artifacts["creation-template"]),
                                     "sha256": sha256(artifacts["creation-template"])},
                "fullCreateInput": {"byteLength": results["constructor-success"][1]["artifact"]["createInputBytes"],
                                    "sha256": results["constructor-success"][1]["artifact"]["createInputSha256"]},
                "runtime": {"byteLength": results["constructor-success"][1]["artifact"]["runtimeBytes"],
                            "sha256": results["constructor-success"][1]["artifact"]["runtimeSha256"]},
                "locatorOffsets": artifacts["offsets"]["locator"],
                "patchControlsValid": True,
            },
            "proof": {
                "artifactProgramCommit": BLANC_ARTIFACT_COMMIT,
                "proofCertificateCommit": BLANC_PROOF_COMMIT,
                "certificate": "first compile-valid pinned-target certificate",
            },
            "positiveIdentityChecks": identity_checks,
        },
        "projection": projection,
        "coverage": {
            "criterion": "71 named rows: every census selector plus constructor; both pause sentinel arms and both exact error polarities; seven role negatives; roles/enumeration; configured-limit validation/consume/exceeded/whole-frame refill; trigger fee/value/router/refund/ETH/events; excludes zero/unlimited and partial-frame limits, nested malformed dynamic ABI, empty/unknown/short dispatch, trailing calldata, and recognized-selector nonpayability",
            "selectorCount": len(selector_rows),
            "selectors": [{"signature": row["signature"], "selector": row["selector"],
                           "rows": selector_rows[row["signature"]]}
                          for row in census["selectors"]],
            "requiredTags": all_tags,
            "deviations": [{"id": deviation, "fields": list(DEVIATION_FIELDS[deviation]),
                            "rows": deviation_rows[deviation]}
                           for deviation in DEVIATION_FIELDS],
        },
        "counts": {
            "rows": len(rows), "agreementRows": sum(case.deviation is None for case in cases),
            "deviationRows": sum(case.deviation is not None for case in cases),
            "selectorCount": len(selector_rows), "constructorRows": sum(case.family == "constructor" for case in cases),
            "resourceBoundaries": len(resources),
            "callTraceEntries": sum(sum(len(trace) for trace in results[case.name][0]["callTrace"])
                                    for case in cases),
        },
        "rows": rows,
        "resourceEvidence": {
            "boundaryDefinition": BOUNDARY_DEFINITION,
            "boundaries": list(resources),
            "namedGasRows": named_gas_rows(resources),
            "vectorSha256": digest(resources),
        },
    }
    manifest["documentFill"] = build_document_fill(
        compatibility_contract(), cases, resources, artifacts, lock, census, projection)
    manifest["sectionDigests"] = {
        key: digest(manifest[key]) for key in (
            "oracle", "artifacts", "projection", "coverage", "counts", "rows",
            "resourceEvidence", "documentFill")
    }
    return manifest


def require_manifest(expected: Mapping, write: bool) -> None:
    encoded = json.dumps(expected, indent=2, sort_keys=True) + "\n"
    if write:
        MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST_PATH.write_text(encoded)
        return
    expect(MANIFEST_PATH.is_file(), "TWG differential manifest is missing")
    committed = MANIFEST_PATH.read_text()
    expect(committed == encoded,
           "TWG differential manifest is stale; regenerate deliberately with --write-manifest")


def live_falsifiers(cases: Sequence[Case], results: Mapping[str, Tuple[Mapping, Mapping]],
                    lock: Mapping, artifacts: Mapping) -> Tuple[int, int]:
    sample = next(case for case in cases if case.name == "trigger-single-exact-fee")
    solidity, blanc = results[sample.name]
    channel_count = 0
    for field in compared_fields(sample):
        broken = copy.deepcopy(blanc)
        if field == "status": broken[field][-1] = "revert"
        elif field in {"returndata", "logs", "callTrace"}: broken[field][-1] = ["corrupt"]
        else: broken[field] = {"corrupt": True}
        expect(field in compare(sample, solidity, broken),
               f"live {field} channel falsifier did not bite")
        channel_count += 1
    corrupt = copy.deepcopy(artifacts)
    corrupt["primary-runtime"] = \
        bytes([artifacts["primary-runtime"][0] ^ 1]) + artifacts["primary-runtime"][1:]
    identity_count = 0
    try:
        validate_identities(lock, json.loads(CENSUS_PATH.read_text()), corrupt)
    except RuntimeError:
        identity_count += 1
    expect(identity_count == 1, "runtime identity falsifier did not bite")
    sentinel = next(case for case in cases if case.name == "pause-for-sentinel")
    broken = copy.deepcopy(results[sentinel.name][1])
    broken["logicalState"]["resumeSince"] = hex(UINT256_MAX - 1)
    expect("logicalState" in compare(sentinel, results[sentinel.name][0], broken),
           "sentinel semantic falsifier did not bite")
    return channel_count, identity_count + 1


def main(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--eels-root", required=True)
    parser.add_argument("--blanc-artifacts", required=True)
    parser.add_argument("--write-manifest", action="store_true")
    parser.add_argument("--manifest-only", action="store_true")
    parser.add_argument("--constructor-probe", action="store_true")
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args(argv)

    eels.verify_eels_pin(Path(args.eels_root).expanduser().resolve(), EELS_PIN, die)
    lock = json.loads(LOCK_PATH.read_text())
    census = json.loads(CENSUS_PATH.read_text())
    artifacts = parse_artifacts(Path(args.blanc_artifacts).read_text())
    identity_checks = validate_identities(lock, census, artifacts)
    cases = build_cases()
    if args.constructor_probe:
        case = cases[0]
        solidity = run_side(case, "solidity", lock, artifacts)
        blanc = run_side(case, "blanc", lock, artifacts)
        assert_case(case, solidity, blanc)
        admin_role = role_hex(DEFAULT_ADMIN_ROLE)
        print(json.dumps({
            "case": case.name,
            "reference": {
                "adminMembers": solidity["logicalState"]["roles"][admin_role]["members"],
                "maximum": solidity["logicalState"]["limit"]["maximum"],
                "previous": solidity["logicalState"]["limit"]["previous"],
                "logsSha256": digest(solidity["logs"]),
            },
            "blanc": {
                "adminMembers": blanc["logicalState"]["roles"][admin_role]["members"],
                "maximum": blanc["logicalState"]["limit"]["maximum"],
                "previous": blanc["logicalState"]["limit"]["previous"],
                "logsSha256": digest(blanc["logs"]),
            },
        }, sort_keys=True))
        return 0
    results: Dict[str, Tuple[Mapping, Mapping]] = {}
    for case in cases:
        solidity = run_side(case, "solidity", lock, artifacts)
        blanc = run_side(case, "blanc", lock, artifacts)
        try:
            assert_case(case, solidity, blanc)
        except RuntimeError:
            if args.verbose:
                differences = compare(case, solidity, blanc)
                print(f"MISMATCH {case.name}: {differences}", file=sys.stderr)
                for field_name in differences:
                    print(f"  {field_name} reference={json.dumps(solidity[field_name], sort_keys=True)[:4000]}", file=sys.stderr)
                    print(f"  {field_name} blanc={json.dumps(blanc[field_name], sort_keys=True)[:4000]}", file=sys.stderr)
                if not differences:
                    for field_name in ("status", "returndata", "logs", "callTrace"):
                        print(f"  semantic-{field_name} reference={json.dumps(solidity[field_name], sort_keys=True)[:4000]}", file=sys.stderr)
                        print(f"  semantic-{field_name} blanc={json.dumps(blanc[field_name], sort_keys=True)[:4000]}", file=sys.stderr)
            raise
        results[case.name] = (solidity, blanc)
    resources = resource_rows(cases, results)
    manifest = build_manifest(cases, results, resources, lock, census, artifacts,
                              identity_checks)
    require_manifest(manifest, args.write_manifest)
    channel_falsifiers, other_live = live_falsifiers(cases, results, lock, artifacts)
    if args.manifest_only:
        print(f"OK — Lido TWG differential manifest: {len(cases)} rows; "
              f"{len(resources)} resource boundaries; 24/24 selectors + constructor; "
              f"5 stable deviations; {channel_falsifiers + other_live} live in-generator falsifiers")
        return 0
    histories = sum(len(case.history) for case in cases)
    traces = sum(sum(len(trace) for trace in results[case.name][0]["callTrace"])
                 for case in cases)
    deviations = sum(case.deviation is not None for case in cases)
    print(f"OK — Lido TWG differential: {len(cases) - deviations} agreement rows + "
          f"{deviations} exact registered-deviation rows; 24/24 selectors + constructor; "
          f"{histories} causal history messages; {len(resources)} resource boundaries; "
          f"{traces} reference CALL/STATICCALL traces; {identity_checks} positive artifact "
          f"checks; {channel_falsifiers + other_live} live channel/identity/semantic falsifiers")
    return 0


if __name__ == "__main__":
    try:
        from ethereum.crypto.hash import keccak256 as _KECCAK
        raise SystemExit(main(sys.argv[1:]))
    except Exception as exc:
        print("REGRESSION — Lido TWG differential: " + str(exc).replace("\n", " "),
              file=sys.stderr)
        raise SystemExit(1)
