"""DRIP blockchain-test encoding through the pinned BPO2 target types.

Loaded only after current_mainnet verifies the isolated interpreter. Header,
RLP and canonical system allocation mechanics follow the existing repository
blockchain generators; no predecessor contract semantics are imported.
"""
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes8, Bytes32, Bytes256
from ethereum_types.numeric import U64, U256, Uint
from ethereum.crypto.hash import keccak256
from ethereum.merkle_patricia_trie import Trie, root as trie_root, trie_set
from ethereum.forks.bpo2.blocks import Header
from ethereum.state import Account, Address
from ethereum.state_mpt import (  # noqa: E402
    State,
    set_account,
    set_storage,
    state_root,
    store_code,
)
from ethereum.utils.hexadecimal import hex_to_bytes
from execution_testing.forks import BPO2 as TestingBPO2

COINBASE = "0x2adc25665018aa1fe0e6bc666dac8fc2697ff9ba"
EMPTY_OMMER_HASH = "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"
EMPTY_TRIE_ROOT = "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"
EMPTY_REQUESTS_HASH = "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
ZERO_HASH = "0x" + "00" * 32
ZERO_BLOOM = "0x" + "00" * 256
MAINNET_BPO2_ACTIVATION_TIMESTAMP = 1_767_747_671
EXPECTED_SYSTEM_ADDRESSES = {
    0x0000F90827F1C53A10CB7A02335B175320002935,
    0x000F3DF6D732807EF1319FB7B8BB8522D0BEAC02,
    0x00000961EF480EB55E80D19AD83579A64C007002,
    0x0000BBDDC7CE488642FB579F8B00F3A590007251,
    0x00000000219AB540356CBB839CBE05303D7705FA,
}
BLOCK_GAS_LIMIT = 30_000_000

def q(n):
    value = int(n, 16) if isinstance(n, str) else int(n)
    digits = format(value, "x")
    return "0x" + ("0" + digits if len(digits) % 2 else digits)

def account(balance, code="0x", storage=None, *, nonce=0):
    return {"nonce": q(nonce), "balance": q(balance), "code": code,
            "storage": {q(k): q(v) for k, v in (storage or {}).items() if v}}

def system_alloc():
    """Materialize BPO2's five canonical system contracts from the target."""
    raw = TestingBPO2.pre_allocation_blockchain()
    if set(raw) != EXPECTED_SYSTEM_ADDRESSES:
        raise RuntimeError(
            f"BPO2 system-contract population differs: {sorted(hex(x) for x in raw)}"
        )
    result = {}
    for address, item in sorted(raw.items()):
        code = item.get("code", b"")
        if isinstance(code, bytes):
            code_hex = "0x" + code.hex()
        elif isinstance(code, str) and code.startswith("0x"):
            code_hex = code.lower()
        else:
            raise RuntimeError(f"BPO2 system code has unknown shape at {address:#x}")
        storage = {}
        for slot, value in item.get("storage", {}).items():
            if isinstance(value, bytes):
                value = int.from_bytes(value, "big")
            storage[int(slot)] = int(value)
        result["0x" + format(address, "040x")] = {
            "nonce": q(int(item.get("nonce", 0))),
            "balance": q(int(item.get("balance", 0))),
            "code": code_hex,
            "storage": {q(slot): q(value) for slot, value in sorted(storage.items()) if value},
        }
    return result

def norm_alloc(alloc):
    """Render transition allocs as even-length hex byte strings for Jaune."""
    return {addr: {
        "nonce": q(a.get("nonce", "0x0")),
        "balance": q(a.get("balance", "0x0")),
        "code": a.get("code", "0x"),
        "storage": {q(k): q(v) for k, v in a.get("storage", {}).items()
                    if int(v, 16)},
    } for addr, a in alloc.items()}

def alloc_root(alloc):
    st = State()
    for addr, a in alloc.items():
        code = Bytes(hex_to_bytes(a.get("code", "0x")))
        set_account(st, Address(hex_to_bytes(addr)), Account(
            nonce=Uint(int(a.get("nonce", "0x0"), 16)),
            balance=U256(int(a.get("balance", "0x0"), 16)),
            code_hash=store_code(st, code),
        ))
        for slot, value in a.get("storage", {}).items():
            if int(value, 16):
                set_storage(st, Address(hex_to_bytes(addr)),
                            Bytes32(int(slot, 16).to_bytes(32, "big")), U256(int(value, 16)))
    return "0x" + bytes(state_root(st)).hex()

def header(d):
    h = Header(parent_hash=hex_to_bytes(d["parentHash"]), ommers_hash=hex_to_bytes(d["uncleHash"]),
        coinbase=Address(hex_to_bytes(d["coinbase"])), state_root=hex_to_bytes(d["stateRoot"]),
        transactions_root=hex_to_bytes(d["transactionsTrie"]), receipt_root=hex_to_bytes(d["receiptTrie"]),
        bloom=Bytes256(hex_to_bytes(d["bloom"])), difficulty=Uint(int(d["difficulty"], 16)),
        number=Uint(int(d["number"], 16)), gas_limit=Uint(int(d["gasLimit"], 16)),
        gas_used=Uint(int(d["gasUsed"], 16)), timestamp=U256(int(d["timestamp"], 16)),
        extra_data=Bytes(hex_to_bytes(d["extraData"])), prev_randao=Bytes32(hex_to_bytes(d["mixHash"])),
        nonce=Bytes8(hex_to_bytes(d["nonce"])), base_fee_per_gas=Uint(int(d["baseFeePerGas"], 16)),
        withdrawals_root=hex_to_bytes(d["withdrawalsRoot"]), blob_gas_used=U64(int(d["blobGasUsed"], 16)),
        excess_blob_gas=U64(int(d["excessBlobGas"], 16)),
        parent_beacon_block_root=hex_to_bytes(d["parentBeaconBlockRoot"]), requests_hash=hex_to_bytes(d["requestsHash"]))
    return h, "0x" + bytes(keccak256(rlp.encode(h))).hex()

def legacy_transactions(body):
    """Decode the target's opaque transaction-body entries for block RLP."""
    encoded = rlp.decode(hex_to_bytes(body))
    if not isinstance(encoded, list):
        raise RuntimeError("BPO2 t8n body is not an RLP transaction list")
    transactions = []
    for index, raw in enumerate(encoded):
        if not isinstance(raw, bytes):
            raise RuntimeError(f"BPO2 t8n body entry {index} is not opaque bytes")
        decoded = rlp.decode(raw)
        if not isinstance(decoded, list) or len(decoded) != 9:
            raise RuntimeError(f"BPO2 t8n body entry {index} is not one legacy transaction")
        transactions.append(decoded)
    return transactions


def _minimal_bytes(value):
    """Return the canonical RLP integer payload used by legacy fields."""
    value = int(value)
    return b"" if value == 0 else value.to_bytes((value.bit_length() + 7) // 8, "big")


def validate_serialized_transactions(body, scheduled_transactions):
    """Bind an opaque t8n body to the exact scheduled, signed transactions.

    Decoding a body and checking only that it is a list of nine-field RLP
    entries leaves room for a self-consistent but unrelated transaction list.
    Compare every signed legacy field with the schedule and reproduce each
    EIP-155 signature from its pinned private key.  This authenticates order,
    count, sender, destination, value, calldata, nonce, gas and chain ID
    before the body is put into a block RLP.
    """
    decoded = legacy_transactions(body)
    if len(decoded) != len(scheduled_transactions):
        raise AssertionError("serialized transaction count differs from schedule")
    from spec256k1 import PrivateKey

    for index, (fields, transaction) in enumerate(zip(decoded, scheduled_transactions)):
        if not isinstance(transaction, dict) or transaction.get("type", "0x0") not in ("0x0", "0x00"):
            raise AssertionError(f"transaction {index} is not a legacy scheduled transaction")
        if len(fields) != 9:
            raise AssertionError(f"transaction {index} has unexpected legacy field count")

        nonce = int(transaction["nonce"], 16)
        gas_price = int(transaction["gasPrice"], 16)
        gas = int(transaction["gas"], 16)
        value = int(transaction.get("value", "0x0"), 16)
        data = hex_to_bytes(transaction.get("input", "0x"))
        destination = hex_to_bytes(transaction.get("to", "0x"))
        if destination and len(destination) != 20:
            raise AssertionError(f"transaction {index} destination is not 20 bytes")
        expected = (nonce, gas_price, gas, destination, value, data)
        actual = (int.from_bytes(fields[0], "big"), int.from_bytes(fields[1], "big"),
                  int.from_bytes(fields[2], "big"), fields[3],
                  int.from_bytes(fields[4], "big"), fields[5])
        if actual != expected:
            raise AssertionError(f"serialized transaction {index} differs from schedule")

        chain_id = int(transaction.get("chainId", "0x1"), 16)
        unsigned = list(fields[:6]) + [_minimal_bytes(chain_id), b"", b""]
        digest = bytes(keccak256(rlp.encode(unsigned)))
        secret_key = int(transaction["secretKey"], 16)
        signer = PrivateKey(secret_key.to_bytes(32, "big"))
        expected_sender = derive_address(secret_key)
        signature = signer.sign_recoverable(digest)
        if len(signature) != 65:
            raise AssertionError(f"transaction {index} signer returned malformed signature")
        expected_r = int.from_bytes(signature[:32], "big")
        expected_s = int.from_bytes(signature[32:64], "big")
        recovery_id = int(signature[64])
        expected_v = 35 + 2 * chain_id + recovery_id
        actual_v = int.from_bytes(fields[6], "big")
        actual_r = int.from_bytes(fields[7], "big")
        actual_s = int.from_bytes(fields[8], "big")
        if (actual_v, actual_r, actual_s) != (expected_v, expected_r, expected_s):
            raise AssertionError(f"serialized transaction {index} signature/sender differs from schedule {expected_sender}")


def transactions_trie_root(body):
    """Compute the pinned target's un-secured trie root for a signed body."""
    encoded = rlp.decode(hex_to_bytes(body))
    if not isinstance(encoded, list):
        raise RuntimeError("BPO2 t8n body is not an RLP transaction list")
    trie = Trie(secured=False, default=None)
    for index, raw in enumerate(encoded):
        if not isinstance(raw, bytes):
            raise RuntimeError(f"BPO2 t8n body entry {index} is not opaque bytes")
        trie_set(trie, rlp.encode(Uint(index)), raw)
    return "0x" + bytes(trie_root(trie)).hex()

def genesis_header(alloc):
    return {
        "parentHash": ZERO_HASH,
        "uncleHash": EMPTY_OMMER_HASH,
        "coinbase": "0x" + "00" * 20,
        "stateRoot": alloc_root(alloc),
        "transactionsTrie": EMPTY_TRIE_ROOT,
        "receiptTrie": EMPTY_TRIE_ROOT,
        "bloom": ZERO_BLOOM,
        "difficulty": "0x00",
        "number": "0x00",
        "gasLimit": q(BLOCK_GAS_LIMIT),
        "gasUsed": "0x00",
        "timestamp": q(MAINNET_BPO2_ACTIVATION_TIMESTAMP),
        "extraData": "0x00",
        "mixHash": ZERO_HASH,
        "nonce": "0x0000000000000000",
        "baseFeePerGas": "0x07",
        "withdrawalsRoot": EMPTY_TRIE_ROOT,
        "blobGasUsed": "0x00",
        "excessBlobGas": "0x00",
        "parentBeaconBlockRoot": ZERO_HASH,
        "requestsHash": EMPTY_REQUESTS_HASH,
    }


def derive_address(key):
    from spec256k1 import PrivateKey
    public = PrivateKey(key.to_bytes(32, "big")).public_key.format(compressed=False)
    return "0x" + bytes(keccak256(public[1:]))[-20:].hex()


def create_address(sender, nonce):
    return "0x" + bytes(keccak256(rlp.encode([hex_to_bytes(sender), Uint(nonce)])))[-20:].hex()


def environment(parent, parent_hash, timestamp, hashes):
    if timestamp <= int(parent["timestamp"], 16):
        raise AssertionError("linked block timestamp must increase")
    return {
        "currentCoinbase": COINBASE, "currentGasLimit": parent["gasLimit"],
        "currentNumber": q(int(parent["number"], 16)+1), "currentTimestamp": q(timestamp),
        "currentRandom": ZERO_HASH, "parentHash": parent_hash,
        "parentTimestamp": parent["timestamp"], "parentDifficulty": "0x0",
        "parentUncleHash": EMPTY_OMMER_HASH, "parentGasLimit": parent["gasLimit"],
        "parentGasUsed": parent["gasUsed"], "parentBaseFee": parent["baseFeePerGas"],
        "parentBlobGasUsed": parent["blobGasUsed"], "parentExcessBlobGas": parent["excessBlobGas"],
        "parentBeaconBlockRoot": ZERO_HASH,
        "blockHashes": {str(number): value for number, value in hashes.items()},
        "ommers": [], "withdrawals": [],
    }


def block_header(parent_hash, env, result):
    return {
        "parentHash": parent_hash, "uncleHash": EMPTY_OMMER_HASH, "coinbase": COINBASE,
        "stateRoot": result["stateRoot"], "transactionsTrie": result["txRoot"],
        "receiptTrie": result["receiptsRoot"], "bloom": result["logsBloom"],
        "difficulty": "0x00", "number": env["currentNumber"], "gasLimit": env["currentGasLimit"],
        "gasUsed": q(result["gasUsed"]), "timestamp": env["currentTimestamp"],
        "extraData": "0x", "mixHash": env["currentRandom"], "nonce": "0x0000000000000000",
        "baseFeePerGas": q(result["currentBaseFee"]), "withdrawalsRoot": result["withdrawalsRoot"],
        "blobGasUsed": q(result["blobGasUsed"]), "excessBlobGas": q(result["currentExcessBlobGas"]),
        "parentBeaconBlockRoot": env["parentBeaconBlockRoot"], "requestsHash": result["requestsHash"],
    }


def fixture(name, alloc, genesis, genesis_hash, blocks, post, last_hash, profile):
    genesis_value, _ = header(genesis)
    schedule = profile["execution"]["blobSchedule"]
    return {f"blanc/drip::{name}[fork_BPO2-blockchain_test]": {
        "network": "BPO2", "genesisBlockHeader": {**genesis, "hash": genesis_hash},
        "pre": norm_alloc(alloc), "postState": norm_alloc(post), "lastblockhash": last_hash,
        "config": {"network": "BPO2", "chainid": "0x01", "blobSchedule": {"BPO2": {
            "target": q(schedule["targetBlobsPerBlock"]), "max": q(schedule["maxBlobsPerBlock"]),
            "baseFeeUpdateFraction": q(schedule["baseFeeUpdateFraction"]),
        }}},
        "genesisRLP": "0x" + bytes(rlp.encode([genesis_value, [], [], []])).hex(),
        "blocks": blocks, "sealEngine": "NoProof",
    }}


def encoded_block(header_json, body):
    value, _ = header(header_json)
    return {"rlp": "0x" + bytes(rlp.encode([value, legacy_transactions(body), [], []])).hex(),
            "blocknumber": str(int(header_json["number"], 16))}


def creation_transaction(secret_key, nonce, creation_code, *, value=0, gas=1_000_000,
                         gas_price=10):
    """Return a signed legacy CREATE transaction input.

    Omitting ``to`` is material: a transaction aimed at an account containing
    the same bytes exercises a normal call and never tests constructor
    semantics.  The caller separately derives and checks the CREATE address.
    """
    if isinstance(creation_code, bytes):
        creation_code = "0x" + creation_code.hex()
    if not isinstance(creation_code, str) or not creation_code.startswith("0x"):
        raise ValueError("creation code must be a 0x-prefixed byte string")
    return {
        "type": "0x0", "chainId": "0x1", "nonce": q(nonce),
        "gasPrice": q(gas_price), "gas": q(gas), "value": q(value),
        "input": creation_code,
        "secretKey": "0x" + int(secret_key).to_bytes(32, "big").hex(),
    }


def group_by_timestamp(scheduled_transactions, *, genesis_timestamp):
    """Group ordered transactions into linked blocks without losing order.

    Each item is ``{"timestamp": int, "transaction": dict}``.  Equal
    timestamps intentionally share one block; different timestamps always
    produce strictly increasing linked block headers.
    """
    groups = []
    transaction_count = 0
    previous = genesis_timestamp
    for index, item in enumerate(scheduled_transactions):
        if set(item) != {"timestamp", "transaction"}:
            raise ValueError(f"scheduled transaction {index} has unexpected keys")
        timestamp = item["timestamp"]
        if type(timestamp) is not int or timestamp <= previous:
            # The first transaction may be at the first post-genesis time,
            # while subsequent transactions may share that block timestamp.
            if groups and timestamp == groups[-1]["timestamp"]:
                groups[-1]["transactions"].append(item["transaction"])
                transaction_count += 1
                continue
            raise ValueError("block timestamps must increase after genesis")
        groups.append({"timestamp": timestamp, "transactions": [item["transaction"]],
                       "offset": transaction_count})
        transaction_count += 1
        previous = timestamp
    return groups


def linked_block_header(parent_hash, environment_value, result):
    """Build the canonical header from one explicit BPO2 transition result."""
    return {
        "parentHash": parent_hash, "uncleHash": EMPTY_OMMER_HASH,
        "coinbase": COINBASE, "stateRoot": result["stateRoot"],
        "transactionsTrie": result["txRoot"], "receiptTrie": result["receiptsRoot"],
        "bloom": result["logsBloom"], "difficulty": "0x00",
        "number": environment_value["currentNumber"],
        "gasLimit": environment_value["currentGasLimit"],
        "gasUsed": q(result["gasUsed"]),
        "timestamp": environment_value["currentTimestamp"], "extraData": "0x",
        "mixHash": environment_value["currentRandom"], "nonce": "0x0000000000000000",
        "baseFeePerGas": q(result["currentBaseFee"]),
        "withdrawalsRoot": result.get("withdrawalsRoot", EMPTY_TRIE_ROOT),
        "blobGasUsed": q(result.get("blobGasUsed", "0x00")),
        "excessBlobGas": q(result.get("currentExcessBlobGas", "0x00")),
        "parentBeaconBlockRoot": environment_value["parentBeaconBlockRoot"],
        "requestsHash": result["requestsHash"],
    }


def execute_linked_blocks(alloc, scheduled_transactions, *, run_transition,
                          prefix_checker=None):
    """Execute and serialize a linked chain, checking every tx prefix.

    ``run_transition`` is the generator's identity-checked ``run_t8n``
    closure.  Prefix replays start from the same block pre-state and are used
    to authenticate each intermediate post-state; the final block transition
    is the only result serialized into the fixture.  No caller-provided final
    state is trusted as a substitute for these replays.
    """
    genesis = genesis_header(alloc)
    genesis_value, genesis_hash = header(genesis)
    current_alloc = alloc
    parent_hash = genesis_hash
    parent = genesis
    history = {0: genesis_hash}
    blocks = []
    receipts = []
    groups = group_by_timestamp(
        scheduled_transactions,
        genesis_timestamp=int(genesis["timestamp"], 16),
    )
    for group in groups:
        timestamp = group["timestamp"]
        environment_value = environment(parent, parent_hash, timestamp, history)
        transactions = group["transactions"]
        output = run_transition(current_alloc, environment_value, transactions)
        result = output.result
        if result.get("rejected") != []:
            raise AssertionError(f"transition rejected transactions: {result['rejected']!r}")
        if len(result.get("receipts", [])) != len(transactions):
            raise AssertionError("receipt count differs from transaction count")
        validate_serialized_transactions(output.body, transactions)
        if transactions_trie_root(output.body) != result.get("txRoot"):
            raise AssertionError("serialized transaction trie root differs from t8n txRoot")
        def receipts_with_gas(value):
            previous = 0
            copied = []
            for receipt in value.get("receipts", []):
                if "cumulativeGasUsed" not in receipt:
                    raise AssertionError("receipt omits cumulativeGasUsed")
                cumulative = int(receipt["cumulativeGasUsed"], 16)
                if cumulative < previous:
                    raise AssertionError("receipt cumulative gas decreases")
                item = dict(receipt)
                item["gasUsed"] = q(cumulative - previous)
                copied.append(item)
                previous = cumulative
            return copied
        full_receipts = receipts_with_gas(result)
        # A prefix replay catches an intermediate state that a later
        # transaction could overwrite before the block's final post-state.
        prefix_alloc = current_alloc
        for tx_index in range(len(transactions)):
            prefix = run_transition(current_alloc, environment_value,
                                    transactions[:tx_index + 1])
            if prefix.result.get("rejected") != []:
                raise AssertionError(f"prefix {tx_index} rejected unexpectedly")
            if prefix_checker is not None:
                prefix_result = dict(prefix.result)
                prefix_result["receipts"] = receipts_with_gas(prefix.result)
                prefix_checker(
                    len(blocks), group["offset"] + tx_index, prefix_alloc, prefix.alloc,
                    prefix_result,
                )
            if tx_index + 1 == len(transactions):
                if prefix.alloc != output.alloc:
                    raise AssertionError("final transaction prefix differs from block post-state")
                for key in ("stateRoot", "txRoot", "receiptsRoot", "logsBloom", "gasUsed"):
                    if prefix.result.get(key) != result.get(key):
                        raise AssertionError(f"final transaction prefix differs in {key}")
                if prefix.body != output.body:
                    raise AssertionError("final transaction prefix differs in encoded body")
            prefix_alloc = prefix.alloc
        block = linked_block_header(parent_hash, environment_value, result)
        block_hash = header(block)[1]
        blocks.append(encoded_block(block, output.body))
        receipts.extend(full_receipts)
        current_alloc = output.alloc
        parent, parent_hash = block, block_hash
        history[int(block["number"], 16)] = block_hash
    return {
        "genesis": {**genesis, "hash": genesis_hash},
        "genesisRLP": "0x" + bytes(rlp.encode([genesis_value, [], [], []])).hex(),
        "blocks": blocks, "post": current_alloc, "lastblockhash": parent_hash,
        "receipts": receipts,
    }
